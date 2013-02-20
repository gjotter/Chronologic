{-# LANGUAGE MultiParamTypeClasses #-} 
module TypeInference 
    where

import AST

import Control.Monad.State
import Data.List
import Data.SBV
import Debug.Trace
import qualified Data.IntervalMap.Interval as I

type Constraint a = (MetaType a, MetaType a)
type Substitution a = (MetaType a, MetaType a)

instance Ord TimeType where
    (TimeBound i11 o11) <= (TimeBound i21 o21)
        | i11 > i21 = False
        | otherwise = True
    (TimeBound _ _) <= (TimeLiteral _) = True
    (TimeLiteral _) <= (TimeBound _ _) = False
    t1 <= t2 = error $ show t1 ++ " <= " ++ show t2
        
data TypeState = TypeState
               { context            :: Context
               , typeconstraints    :: [Constraint BoundType]
               , timeconstraints    :: [(TimeType,TimeType)]
               , uniqueTypeVar      :: VariableIndex
               , uniqueTimeVar      :: VariableIndex
               }

data PrimitiveRecord = PrimitiveRecord [Substitution PrimitiveType]

data TimeRecord = TimeRecord 
                { timeSubs :: [Substitution TimeType]
                , timeVars :: [(TimeType,TimeType)] }

class Eq a => Substitutable z a where
    add :: Substitution a -> z -> z
    apply :: ([Substitution a] -> [Substitution a]) -> z -> z 
    match :: MetaType a -> MetaType a -> z -> z 

instance Substitutable TimeRecord TimeType where
    add x tr = tr { timeSubs = x : (timeSubs tr) }
    apply f tr = tr { timeSubs = f $ timeSubs tr }
    match (Constant x) (Constant y) tr = let maysub = matchConstantType x y
                                         in case maysub of
                                                Just z -> tr { timeVars = z : (timeVars tr)}
                                                Nothing -> tr
        where 
            matchConstantType (TimeBound i1 o1) (TimeBound i2 o2) 
                | i1 == i2  = Nothing
                | otherwise = Just (TimeBound i1 o1,TimeBound i2 o2)
     
            matchConstantType (TimeLiteral o1 ) (TimeLiteral o2 ) 
                | o1 == o2  = Nothing 
                | otherwise = error "cannot unify literals o1 o2"
    
            matchConstantType t1@(TimeBound i1 o1) t2@(TimeLiteral o2 ) = Just (t2,t1)
   
            matchConstantType t1@(TimeLiteral o1 ) t2@(TimeBound i2 o2) = matchConstantType t2 t1
    

instance Substitutable PrimitiveRecord PrimitiveType where
    add x (PrimitiveRecord xs) = PrimitiveRecord (x:xs)
    apply f (PrimitiveRecord xs) = PrimitiveRecord $ f xs
    match (Constant x) (Constant y) tr 
        | x == y = tr
        | otherwise = error "x /= y"

-- Replace either type variables or concrete types when matched
(|->) :: Eq a => MetaType a -> MetaType a -> [(MetaType a, MetaType a)] -> [(MetaType a,MetaType a)]
from |-> to = map (\(t1,t2) -> (replaceIn t1,replaceIn t2)) 
    where 
        replaceIn x = case x of 
            Arrow t1 t2 -> Arrow (replaceIn t1) (replaceIn t2)
            _           -> if x == from then to else x

tmap f (t1,t2) = (f t1,f t2)
 
-- Map over individual metatypes, only changing the concrete types
-- useful for changing between Type and PrimitiveType or TimedType
transformMetaType :: (a -> b) -> MetaType a -> MetaType b
transformMetaType f (Arrow t1 t2) = Arrow (transformMetaType f t1) (transformMetaType f t2)
transformMetaType f (Var i)       = Var i
transformMetaType f (Constant t)  = Constant $ f t

emptyState = TypeState [] [] [] 0 0

simpleTimeVar :: State TypeState Int
simpleTimeVar = 
    do  i <- gets uniqueTimeVar
        modify (\s -> s { uniqueTimeVar = (i+1) })
        return i
        
simpleTypeVar :: State TypeState Int
simpleTypeVar = 
    do  i <- gets uniqueTypeVar
        modify (\s -> s { uniqueTypeVar = (i+1) })
        return i

freshTypeVar :: State TypeState (MetaType a)
freshTypeVar = 
    do  i <- gets uniqueTypeVar
        modify (\s -> s { uniqueTypeVar = (i+1) })
        return $ Var i

freshTimeVar :: State TypeState (MetaType a)
freshTimeVar = 
    do  i <- gets uniqueTimeVar
        modify (\s -> s { uniqueTimeVar = (i+1) })
        return $ Var i

index2Name :: Int -> State TypeState (String,Binding)
index2Name i = 
    do  ctx <- gets context
        return $ ctx !! i

context2BoundType :: DeBruijn -> State TypeState (MetaType BoundType)
context2BoundType db =
    do  ctx <- gets context
        return $ ctx2Type ctx db
            
addContextBinding :: (String,Binding) -> State TypeState ()
addContextBinding c = 
    do  ctx <- gets context
        modify (\s -> s { context = c : ctx })

addTypeConstraints :: [Constraint BoundType] -> State TypeState ()
addTypeConstraints c =
    do  constr <- gets typeconstraints
        modify (\s -> s { typeconstraints = c ++ constr })

selectPrimitive :: BoundType -> PrimitiveType
selectPrimitive (BoundType pr _) = pr

selectTimeType :: BoundType -> TimeType
selectTimeType (BoundType _ tt) = tt

printTypeMap cs = 
    do  s <- typecheck cs
        mapM_ (putStrLn . show) $ snd s

printTimeSat = (liftM fst) . typecheck

typecheck cs = 
    do  let subs f e              = unify (map (tmap $ transformMetaType f) cs) e
            (PrimitiveRecord prs) = subs selectPrimitive $ PrimitiveRecord []
            tts                   = subs selectTimeType $ TimeRecord [] []
            mergedmap             = merge prs (timeSubs tts)
            pred                  = buildproof (timeVars tts)
        s <- sat pred
        return (s,mergedmap)

buildproof cs =  
    do  let ordtimevars           = fixOrder cs
            numtimevars           = length $ filterVariables ordtimevars
            proof                 = do syms <- mkExistVars numtimevars
                                       return $ map (createConstraints syms) ordtimevars
        join $ liftM sequence_ proof
        solve []
                       
createConstraints ss (TimeBound i1 o1,TimeBound i2 o2)
    =   let (s1,s2) = (ss !! i1, ss !! i2)
        in  constrain $ s1 + o1 .>= s2 + o2
createConstraints ss (TimeBound i1 o1,TimeLiteral  o2)
    =   let s1 = ss !! i1
        in  constrain $ s1 .>= o2
createConstraints _ t = error $ "wrong input " ++ show t ++ " "

filterVariables :: [(TimeType,TimeType)] -> [TimeType]
filterVariables xs = nubBy equalIdentifier $ map fst xs
   where 
   equalIdentifier (TimeBound i1 o1) (TimeBound i2 o2)
        | i1 == i2  = True
        | otherwise = False

fixOrder :: [(TimeType,TimeType)] -> [(TimeType,TimeType)]
fixOrder = map fixOrder' -- . sort
    where
    fixOrder' (t1@(TimeBound i1 o1), t2@(TimeBound i2 o2))
        | i1 < i2   = (t1,t2)
        | otherwise = (t2,t1)
    fixOrder' (t1@(TimeLiteral o2), t2@(TimeBound i1 o1)) = (t2,t1)
    fixOrder' (t1,t2) = (t1,t2)

-- merges timed types with primitive types. Substitutions
-- should have the same form, otherwise something has gone wrong in
-- one of the algorithms.
merge = zipWith (ftuple merge')
    where
        ftuple f (t1,t2) (u1,u2) = (f t1 u1,f t2 u2)

        -- only merge identicals, otherwise error
        merge' (Var x) (Var y) 
            | x == y = Var x
            | otherwise = error "Var x /= Var y in merging types"
        merge' (Arrow x1 x2) (Arrow y1 y2) = Arrow (merge' x1 y1) (merge' x2 y2)
        merge' (Constant x) (Constant y) = Constant $ BoundType x y
        merge' x y = error $ "merging " ++ show x ++ " and " ++ show y

splitLiterals = partition isBoundTimeVar
    where 
        -- only select the items which bind a time variable to a literal
        isBoundTimeVar (TimeLiteral _, TimeBound _ _) = True
        isBoundTimeVar (TimeBound _ _, TimeLiteral _) = True
        isBoundTimeVar _                                = False

unify :: (Show a, Substitutable z a) => [Constraint a] -> z -> z
unify [] r = id r
unify (c:cs) r = case c of
    (Constant t1, Constant t2)      -> unify cs $ match (Constant t1) (Constant t2) r
    (Arrow s1 s2, Arrow t1 t2)      -> unify ((s1,t1) : (s2,t2) : cs) r
    (tyS@(Var idS), tyT      ) 
        | tyS == tyT                ->  unify cs r
        | not $ idS `isFVIn` tyT    ->  let cs' = (tyS |-> tyT) cs
                                            r'  = add (tyS,tyT) $ apply (tyS |-> tyT) r 
                                        in  unify cs' r'

    (tyS, tyT@(Var idT)      )      -> unify ((tyT,tyS) : cs) r
    (t1,t2                   )      -> error "not unifiable " 

-- doest the type 'ty' contain a variable with 'id'
isFVIn id ty = case ty of
    Arrow t1 t2   -> isFVIn id t1 || isFVIn id t2
    Var id'       -> id' == id
    Constant _    -> False


filterOutputs = uncurry (++) . filterOutputs' . unzip
    where 
    filterOutputs' = tmap $ foldr ($) [] . map buildList . filter isArrow
    buildList t = case filterOutput t of
                        Just x  -> (x :)
                        Nothing -> id

isArrow (Arrow _ _) = True
isArrow _           = False 
        
filterOutput :: MetaType TimeType -> Maybe (TimeType)
filterOutput t = 
    case t of 
        Arrow x y  -> filterOutput y
        Var _      -> Nothing
        Constant x -> Just x

constraints :: Term -> State TypeState (MetaType BoundType)
constraints tm = case tm of

    TmAbs str tm ->
        do  nvlam <- freshTypeVar
            addContextBinding (str,TyVarBind nvlam)
            nvtot <- freshTypeVar
            ty <- constraints tm
            addTypeConstraints [(nvtot,Arrow nvlam ty)]
            return nvtot
 
    TmTAbs str tm ->
        do  nv <- freshTimeVar
            addContextBinding (str,TyVarBind nv)
            constraints tm 

    TmApp t1 t2 ->
        do  ty1 <- constraints t1
            ty2 <- constraints t2
            nv <- freshTypeVar
            addTypeConstraints [(ty1,Arrow ty2 nv)]
            return nv

    TmAs tm ty -> 
        do  tytm <- constraints tm
            ty' <- bindType ty
            addTypeConstraints [(tytm,ty')]
            return tytm

    TmAdd t1 t2 ->
        do  ty1 <- constraints t1
            ty2 <- constraints t2
            nv <- freshTypeVar
            addTypeConstraints [(ty1,nv)]
            addTypeConstraints [(nv,ty2)]
            return nv

    TmVar k -> 
        do  ty <- var2Type k 
            return ty
    
    TmLet lb tm ->
        do  mapM constrainLet lb 
            constraints tm

    TmTime ptm ctm -> 
        do  nv <- freshTypeVar
            let ct = Constant $ BoundType (typePTerm ptm) (typeCTerm ctm)
            addTypeConstraints [(nv,ct)]
            return nv

-- Bind the type, which may include an unbound time quantifier
-- to a specific time quantifier 
-- in other words: switch the DeBruijn index used in (TimeUnbound db offset) 
-- to the actual time quantifier used
bindType :: MetaType UnboundType -> State TypeState (MetaType BoundType)
bindType t = case t of
    Var db                          -> context2BoundType db 
    Arrow t1 t2                     ->  do  ty1 <- bindType t1
                                            ty2 <- bindType t2
                                            return $ Arrow ty1 ty2
    Constant (UnboundType pt tt)    -> case tt of
        TimeUnbound db o ->  
            do  ty <- context2BoundType db
                case ty of 
                    (Var i) -> return $ Constant $ BoundType pt $ TimeBound i o
                    _       -> error "cant bind time to non-variable"

-- Calculate the constraints of a let binding
-- This consists of first checking the constraints of the right hand side of the let
-- binding, then unifying it to obtain a principal type
-- By adding this to the context as a typescheme we know, whenever it is referenced later,
-- we will need to create an instance of this type.
constrainLet :: (String,Term) -> State TypeState ()
constrainLet (str,tm) = 
    do  ctx <- gets context
        unTy <- gets uniqueTypeVar
        unTi <- gets uniqueTimeVar
        tc <- gets timeconstraints
        let ts       = TypeState ctx [] [] unTy unTi
            (t1,ts') = runState (constraints tm >>= return) ts
            (tc',ts'') = undefined --typecheck $ typeconstraints ts'
            princty  = lookup t1 ts''
        modify (\s -> s { uniqueTypeVar = uniqueTypeVar ts' })
        modify (\s -> s { timeconstraints = tc ++ tc' })
        case princty of 
                Just t  -> addContextBinding (str,TyScheme t)
                Nothing -> error "looked up invalid binder in let"

-- Lookup the type the variable is refering to.
-- In case this is a typescheme we first need to create a specific instance for 
-- the typescheme, since it could be polymorphic
var2Type k = 
    do  (_,bind) <- index2Name k
        case bind of 
            TyScheme t  -> liftM fst $ instantiatePoly t []
            _           -> context2BoundType k

-- Instantiating a polymorphic type into a specifc type involves
-- changing all free variables in new variables that can be bound to a specific
-- type. But to do so we need to do this consistently, namely all X in the type
-- need to change to Y, not X_1 |-> Y and X_2 |-> Z. To do so I use a list of 
-- replacements.
instantiatePoly 
    :: MetaType BoundType -> [(MetaType BoundType,MetaType BoundType)] 
    -> State TypeState (MetaType BoundType,[(MetaType BoundType,MetaType BoundType)])
instantiatePoly t replaced = 
    case t of
        Arrow t1 t2   ->  do  (ty1,tr1) <- instantiatePoly t1 replaced
                              (ty2,tr2) <- instantiatePoly t2 (replaced ++ tr1)
                              return (Arrow ty1 ty2,tr1++tr2)
        Constant (BoundType pt tt) -> 
            case tt of
                TimeBound i o -> instantiateTimeType i o pt replaced
                _               -> return (t,[])

        -- We can only replace if it wasn't replaced before and the context does not
        -- bind the variable.
        Var k ->  
            do  let r = lookup t replaced
                ctx <- gets context
                if isInContext ctx k 
                    then return (t,[])
                    else case r of
                            Just v  ->  return (v,[])
                            Nothing ->  do nv <- freshTypeVar
                                           return (nv,[(t,nv)])

instantiateTimeType b o pt replaced = 
    do  let replacement = lookup (Var b) replaced
        case replacement of
            Just (Var i) -> return (Constant $ BoundType pt $ (TimeBound i o) , [])
            Nothing        -> do  sv <- simpleTimeVar
                                  let t'      = Constant $ BoundType pt (TimeBound sv o)
                                      replace = (Var b, Var sv)
                                  return (t', [replace]) 

typePTerm (TmBool _)    = TyBool
typePTerm (TmInt _)     = TyInt

typeCTerm (TmOffset o) = TimeLiteral o

b0 = TmTime (TmBool True) (TmOffset 0)
b1 = TmTime (TmBool True) (TmOffset 1)

delay = TmTAbs "n" $ TmAs (TmAbs "x" (TmVar 0)) $ 
        Arrow (Constant $ UnboundType TyBool (TimeUnbound 1 0)) 
        (Constant $ UnboundType TyBool (TimeUnbound 1 1))

f = TmTAbs "n" $ TmAs (TmAbs "x" $ TmAbs "y" (TmVar 0)) $ 
        Arrow (Constant $ UnboundType TyBool (TimeUnbound 2 0)) 
        (Arrow (Constant $ UnboundType TyBool (TimeUnbound 2 1)) 
        (Constant $ UnboundType TyBool (TimeUnbound 2 2)))

g = (TmApp (TmApp f (TmApp delay b0)) (TmApp delay b0))
h = (TmApp (TmApp f (TmApp delay b0)) b0)

testcsg= fst $ runState (constraints g >> gets typeconstraints) emptyState
testcsg'= fst $ runState (constraints g) emptyState
testcsh = fst $ runState (constraints h >> gets typeconstraints) emptyState
testcsh' = fst $ runState (constraints h) emptyState
