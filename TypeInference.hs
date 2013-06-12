{-# LANGUAGE MultiParamTypeClasses #-} 
module TypeInference 
    where

import AST

import Control.Monad.State
import Data.List
import Data.SBV
import Debug.Trace

type Constraint a = (MetaType a, MetaType a)
type Substitution a = (MetaType a, MetaType a)

instance Ord BoundedTime where
    (BoundedTime i11 o11) <= (BoundedTime i21 o21)
        | i11 > i21 = False
        | otherwise = True
    (BoundedTime _ _) <= (TimeLiteral _) = True
    (TimeLiteral _) <= (BoundedTime _ _) = False
    t1 <= t2 = error $ show t1 ++ " <= " ++ show t2
        
data TypeState = TypeState
               { context            :: Context
               , typeconstraints    :: [Constraint BoundedType]
               , timeconstraints    :: [(BoundedTime,BoundedTime)]
               , uniqueTypeVar      :: VariableIndex
               , uniqueTimeVar      :: VariableIndex
               }

data PrimitiveRecord = PrimitiveRecord [Substitution PrimitiveType]

data TimeRecord = TimeRecord 
                { timeSubs :: [Substitution BoundedTime]
                , timeVars :: [(BoundedTime,BoundedTime)] }

-- Substitutable typeclass to allow a single unification algorithm on
-- both time variables as regular type variables
class Eq a => Substitutable z a where
    add :: Substitution a -> z -> z
    apply :: ([Substitution a] -> [Substitution a]) -> z -> z 
    match :: MetaType a -> MetaType a -> z -> z 

-- TODO: this should/could probably be done a lot more elegantly and readable..
instance Substitutable TimeRecord BoundedTime where
    add x tr = tr { timeSubs = x : (timeSubs tr) }
    apply f tr = tr { timeSubs = f $ timeSubs tr }
    match (Constant x) (Constant y) tr = let maysub = matchConstantType x y 
                                         in case maysub of
                                                Just z -> tr { timeVars = z : (timeVars tr)}
                                                Nothing -> tr
        where 
            matchConstantType (BoundedTime i1 o1) (BoundedTime i2 o2) 
                | i1 == i2  = Nothing
                | otherwise = Just (BoundedTime i1 o1,BoundedTime i2 o2)
     
            matchConstantType (TimeLiteral o1 ) (TimeLiteral o2 ) 
                | o1 == o2  = Nothing 
                | otherwise = error "cannot unify literals o1 o2"
    
            matchConstantType t1@(BoundedTime i1 o1) t2@(TimeLiteral o2 ) = Just (t2,t1)
   
            matchConstantType t1@(TimeLiteral o1 ) t2@(BoundedTime i2 o2) = matchConstantType t2 t1
    

instance Substitutable PrimitiveRecord PrimitiveType where
    add x (PrimitiveRecord xs) = PrimitiveRecord (x:xs)
    apply f (PrimitiveRecord xs) = PrimitiveRecord $ f xs
    match (Constant x) (Constant y) tr 
        | x == y = tr
        | otherwise = error $ show x ++ " /= " ++ show y

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

emptyState = TypeState (Context [] [] []) [] [] 0 0

-- Some useful functions for modifying the typestate
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

deBruijn2Var :: (Show a, Show b) => (Context -> [(a,b)]) -> Int -> State TypeState b
deBruijn2Var f i = 
    do  ctx <- gets context
        let binding = index2name (f ctx) i
        return $ snd binding

addTypeVarBinding :: TypeVarBinding -> State TypeState ()
addTypeVarBinding c = 
    do  ctx <- gets context
        let ctx' = ctx { typeVarBind = c : (typeVarBind ctx) }
        modify (\s -> s { context = ctx' })

addSchemeBinding :: SchemeBinding -> State TypeState ()
addSchemeBinding c = 
    do  ctx <- gets context
        let ctx' = ctx { schemeBind = c : schemeBind ctx }
        modify (\s -> s { context = ctx' })

addTimeVarBinding :: TimeVarBinding -> State TypeState ()
addTimeVarBinding c = 
    do  ctx <- gets context
        let ctx' = ctx { timeVarBind = c : timeVarBind ctx }
        modify (\s -> s { context = ctx' })

addTypeConstraints :: [Constraint BoundedType] -> State TypeState ()
addTypeConstraints c =
    do  constr <- gets typeconstraints
        modify (\s -> s { typeconstraints = c ++ constr })

selectPrimitive :: BoundedType -> PrimitiveType
selectPrimitive (BoundedType pr _) = pr

selectBoundedTime :: BoundedType -> BoundedTime
selectBoundedTime (BoundedType _ tt) = tt

printTypeMap cs = 
    do  s <- typecheck cs
        mapM_ (putStrLn . show) $ snd s

printTimeSat = (liftM fst) . typecheck

-- Typecheck: unify both primitive types and timed types separately, then
-- merge the two and build a proof of the time variables.
typecheck cs = 
    do  let subs f e              = unify (map (tmap $ transformMetaType f) cs) e
            (PrimitiveRecord prs) = subs selectPrimitive $ PrimitiveRecord []
            tts                   = subs selectBoundedTime $ TimeRecord [] []
            mergedmap             = merge prs (timeSubs tts)
            pred                  = buildproof (timeVars tts)
        s <- sat pred
        return (s,mergedmap)

buildproof cs =  
    do  let ordtimevars           = fixOrder cs
            numtimevars           = length $ filterVariables ordtimevars
            proof                 = do syms <- mkExistVars numtimevars
                                       mapM_ (\s -> constrain $ s .>= 0) syms
                                       return $ map (createConstraints syms) ordtimevars
        join $ liftM sequence_ proof
        solve []
                       
createConstraints ss (BoundedTime i1 o1,BoundedTime i2 o2)
    =   let (s1,s2) = (ss !! i1, ss !! i2)
        in  trace ("constrain " ++ show i1 ++ "+" ++ show o1 ++ " <= " ++ show i2 ++ "+" ++ show o2) $ constrain $ s1 + o1 .<= s2 + o2
createConstraints ss (BoundedTime i1 o1,TimeLiteral  o2)
    =   let s1 = ss !! i1
        in  trace ("constrain " ++ show i1 ++ "+" ++ show o1 ++ " >= " ++ show o2) $ constrain $ s1 + o1 .>= o2
createConstraints _ t = error $ "wrong input " ++ show t ++ " "

filterVariables :: [(BoundedTime,BoundedTime)] -> [BoundedTime]
filterVariables xs = nubBy equalIdentifier $ map fst xs
   where 
   equalIdentifier (BoundedTime i1 o1) (BoundedTime i2 o2)
        | i1 == i2  = True
        | otherwise = False

fixOrder :: [(BoundedTime,BoundedTime)] -> [(BoundedTime,BoundedTime)]
fixOrder = map fixOrder' -- . sort
    where
    fixOrder' (t1@(BoundedTime i1 o1), t2@(BoundedTime i2 o2))
        | i1 < i2   = (t1,t2)
        | otherwise = (t2,t1)
    fixOrder' (t1@(TimeLiteral o2), t2@(BoundedTime i1 o1)) = (t2,t1)
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
        merge' (Constant x) (Constant y) = Constant $ BoundedType x y
        merge' x y = error $ "merging " ++ show x ++ " and " ++ show y

splitLiterals = partition isBoundTimeVar
    where 
        -- only select the items which bind a time variable to a literal
        isBoundTimeVar (TimeLiteral _, BoundedTime _ _) = True
        isBoundTimeVar (BoundedTime _ _, TimeLiteral _) = True
        isBoundTimeVar _                                = False

-- Unification of a substitutable, leading to a set of contraints
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
        
filterOutput :: MetaType BoundedTime -> Maybe (BoundedTime)
filterOutput t = 
    case t of 
        Arrow x y  -> filterOutput y
        Var _      -> Nothing
        Constant x -> Just x

-- Calculate constraints of term tm in the state
constraints :: Term -> State TypeState (MetaType BoundedType)
constraints tm = case tm of

    TmAbs str tm ->
        do  nvlam <- freshTypeVar
            nvtot <- freshTypeVar
            ctx   <- gets context 
            addTypeVarBinding (str,nvlam)
            ty    <- constraints tm
            modify (\s -> s { context = ctx })
            addTypeConstraints [(nvtot,Arrow nvlam ty)]
            trace (show $ typeVarBind ctx) $ return nvtot
 
    TmTAbs str tm ->
        do  nv <- freshTimeVar
            addTimeVarBinding (str,nv)
            constraints tm 

    TmApp t1 t2 ->
        do  ty2 <- constraints t2
            ty1 <- constraints t1
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
            addTypeConstraints [(ty2,nv)]
            return nv

    TmIf t1 t2 t3 ->
        do  ty1 <- constraints t1
            ty2 <- constraints t2
            ty3 <- constraints t3
            ntv <- simpleTimeVar
            let booltype = Constant $ BoundedType TyBool (BoundedTime ntv 0)
            addTimeVarBinding ("ifbind",booltype)
            addTypeConstraints [(ty2,ty3)]
            addTypeConstraints [(ty1,booltype)]
            return ty2

    TmTypeVar k -> 
        do  ty <- deBruijn2Var typeVarBind k
            ctx <- gets context
            trace ("Var " ++ show k ++ ":" ++ (show $ typeVarBind ctx)) $ return ty

    TmTimeVar k ->
        do  ti <- deBruijn2Var timeVarBind k
            return ti
             
    TmSchemeVar k ->
        do  sch <- deBruijn2Var schemeBind k
            liftM fst $ instantiatePoly sch [] 

    TmLet lb tm ->
        do  mapM constrainLet lb 
            constraints tm

    TmTime ptm ctm -> 
        do  nv <- freshTypeVar
            let ct = Constant $ BoundedType (typePTerm ptm) (typeCTerm ctm)
            addTypeConstraints [(nv,ct)]
            return nv

-- Bind the type, which may include an unbound time quantifier
-- to a specific time quantifier 
-- in other words: switch the DeBruijn index used in (UnboundedTime db offset) 
-- to the actual time quantifier used
bindType :: MetaType UnboundedType -> State TypeState (MetaType BoundedType)
bindType t = case t of
    Var db                          ->  deBruijn2Var timeVarBind db 
    Arrow t1 t2                     ->  do  ty1 <- bindType t1
                                            ty2 <- bindType t2
                                            return $ Arrow ty1 ty2
    Constant (UnboundedType pt tt)    -> case tt of
        UnboundedTime db o ->  
            do  ty <- deBruijn2Var timeVarBind db
                case ty of 
                    (Var i) -> return $ Constant $ BoundedType pt $ BoundedTime i o
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
                Just t  -> addSchemeBinding (str,t)
                Nothing -> error "looked up invalid binder in let"

-- Instantiating a polymorphic type into a specifc type involves
-- changing all free variables in new variables that can be bound to a specific
-- type. But to do so we need to do this consistently, namely all X in the type
-- need to change to Y, not X_1 |-> Y and X_2 |-> Z. To do so I use a list of 
-- replacements.
instantiatePoly 
    :: MetaType BoundedType -> [(MetaType BoundedType,MetaType BoundedType)] 
    -> State TypeState (MetaType BoundedType,[(MetaType BoundedType,MetaType BoundedType)])
instantiatePoly t replaced = 
    case t of
        Arrow t1 t2   ->  do  (ty1,tr1) <- instantiatePoly t1 replaced
                              (ty2,tr2) <- instantiatePoly t2 (replaced ++ tr1)
                              return (Arrow ty1 ty2,tr1++tr2)
        Constant (BoundedType pt tt) -> 
            case tt of
                BoundedTime i o -> instantiateBoundedTime i o pt replaced
                _               -> return (t,[])

        -- We can only replace if it wasn't replaced before and the context does not
        -- bind the variable.
        Var k ->  
            do  let r = lookup t replaced
                ctx <- gets context
                if isInContext k $ typeVarBind ctx
                    then return (t,[])
                    else case r of
                            Just v  ->  return (v,[])
                            Nothing ->  do nv <- freshTypeVar
                                           return (nv,[(t,nv)])

instantiateBoundedTime b o pt replaced = 
    do  let replacement = lookup (Var b) replaced
        case replacement of
            Just (Var i) -> return (Constant $ BoundedType pt $ (BoundedTime i o) , [])
            Nothing        -> do  sv <- simpleTimeVar
                                  let t'      = Constant $ BoundedType pt (BoundedTime sv o)
                                      replace = (Var b, Var sv)
                                  return (t', [replace]) 

-- Some example terms, these should probably go somewhere else
typePTerm (TmBool _)    = TyBool
typePTerm (TmInt _)     = TyInt

typeCTerm (TmOffset o) = TimeLiteral o

b0 = TmTime (TmBool True) (TmOffset 0)
i0 = TmTime (TmInt 42) (TmOffset 0)
b1 = TmTime (TmBool True) (TmOffset 1)

delay = TmTAbs "n" $ TmAs (TmAbs "x" (TmTypeVar 0)) $ 
        Arrow (Constant $ UnboundedType TyBool (UnboundedTime 0 0)) 
        (Constant $ UnboundedType TyBool (UnboundedTime 0 1))

delayI = TmTAbs "t" $ TmAs (TmAbs "xd" (TmTypeVar 0)) $ 
        Arrow (Constant $ UnboundedType TyInt (UnboundedTime 0 0)) 
        (Constant $ UnboundedType TyInt (UnboundedTime 0 3))


f = TmTAbs "n" $ TmAs (TmAbs "x" $ TmAbs "y" (TmTypeVar 0)) $ 
        Arrow (Constant $ UnboundedType TyBool (UnboundedTime 0 0)) 
        (Arrow (Constant $ UnboundedType TyBool (UnboundedTime 0 1)) 
        (Constant $ UnboundedType TyBool (UnboundedTime 0 2)))

g = (TmApp (TmApp f (TmApp delay b0)) (TmApp delay b0))
h = TmAbs "x" $ TmApp (TmApp f (TmApp delay (TmTypeVar 0))) (TmTypeVar 0)
k = TmAbs "x" $ TmApp h g

sel = TmTAbs "t" $ TmAs  (TmAbs "p" $ TmAbs "x" $ TmAbs "y" $ (TmIf (TmTypeVar 2) (TmTypeVar 1) (TmTypeVar 0)))
                      (Arrow (Constant $ UnboundedType TyBool (UnboundedTime 0 0))
                            (Arrow (Constant $ UnboundedType TyInt (UnboundedTime 0 0))
                                   (Arrow   (Constant $ UnboundedType TyInt (UnboundedTime 0 1))
                                            (Constant $ UnboundedType TyInt (UnboundedTime 0 2)))))

comp  = TmAbs "pe" $ TmAbs "xe" $ TmApp (TmApp (TmApp sel (TmTypeVar 1)) (TmTypeVar 0)) (TmApp delayI (TmTypeVar 0))
comp' = TmAbs "pe" $ TmAbs "xe" $ TmApp (TmApp (TmApp sel (TmTypeVar 1)) (TmApp delayI (TmTypeVar 0))) (TmTypeVar 0)

compcomp = TmAbs "p" $ TmAbs "x" $ TmApp (TmApp (TmApp sel (TmTypeVar 1)) (TmApp (TmApp comp (TmTypeVar 1)) (TmTypeVar 0))) (TmApp (TmApp comp' (TmTypeVar 1)) (TmTypeVar 0))

comp2 = TmAbs "pe" $ TmAbs "xe" $ TmApp (TmApp (TmApp sel (TmTypeVar 1)) (TmApp (TmApp (TmApp sel (TmTypeVar 1)) (TmTypeVar 0)) (TmApp delayI (TmTypeVar 0)))) (TmTypeVar 0)--(TmApp delayI (TmTypeVar 0))) (TmApp delayI (TmTypeVar 0))
compt = TmApp (TmApp comp b0) i0 

testcsg= fst $ runState (constraints g >> gets typeconstraints) emptyState
testcsg'= fst $ runState (constraints g) emptyState
testcsh = fst $ runState (constraints h >> gets typeconstraints) emptyState
testcsh' = fst $ runState (constraints h) emptyState
testcsk = fst $ runState (constraints k >> gets typeconstraints) emptyState


