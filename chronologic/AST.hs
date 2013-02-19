{-# LANGUAGE TypeSynonymInstances, FlexibleInstances #-}
module AST 
    where

import Control.Applicative
import Data.SBV

type Context = [(String,Binding)]
type LetBind = [(String,Term)]

data Binding = NameBind
             | VarBind (MetaType Type)
             | TyVarBind (MetaType Type)
             | TyScheme (MetaType Type)
             deriving Show

data MetaType a = Arrow (MetaType a) (MetaType a)
                | Var VariableIndex
                | Concrete a
                deriving (Eq,Show)

data Type = Type PrimitiveType TimeType
          deriving (Eq,Show)

data PrimitiveType 
    = TyBool 
    | TyInt
    deriving (Eq,Show)

data TimeType 
    = TimeBound TimeVariableIndex Offset
    | TimeLiteral Offset
    | TimeUnbound DeBruijn Offset
    deriving (Eq,Show)

type TimeVariableIndex = Int
type VariableIndex = Int
type DeBruijn = Int
type Offset = SInteger

data Term = TmVar DeBruijn 
          | TmAbs String Term
          | TmTAbs String Term
          | TmApp Term Term  
          | TmAs Term (MetaType Type)
          | TmAdd Term Term
          | TmIf Term Term Term
          | TmLet LetBind Term
          | TmTime PTerm CTerm
          deriving (Eq,Show)

data PTerm = TmBool Bool
           | TmInt Int
           deriving (Eq,Show)

data CTerm = CTmOffset Offset
    deriving (Eq,Show)

type2Time :: Type -> TimeType 
type2Time (Type pt tt) = tt

mapConcrete :: (a -> a) -> MetaType a -> MetaType a
mapConcrete f t =
    case t of
        Arrow t1 t2 -> Arrow (f `mapConcrete` t1) (f `mapConcrete` t2)
        Concrete x  -> Concrete $ f x
        Var v       -> Var v

mapTyC :: (TimeType -> TimeType) -> MetaType Type -> MetaType Type
mapTyC f t =
    case t of
        Arrow t1 t2           -> Arrow (f `mapTyC` t1) (f `mapTyC` t2)
        Concrete (Type pt tt) -> Concrete $ Type pt (f tt)
        Var v                 -> Var v

emptyContext = []

ctx2Type :: Context -> DeBruijn -> MetaType Type
ctx2Type ctx db = 
    let (_,bind) = index2name ctx db
    in case bind of
        TyScheme t  -> t
        VarBind t   -> t
        TyVarBind t -> t
        _           -> error "looked up invalid binder"

index2name = (!!)


isInContext ct t = foldl (||) False $ map (isInContext' t) ct

isInContext' :: VariableIndex -> (String,Binding) -> Bool
isInContext' vi (_,bind) = 
    case bind of
        TyScheme _  -> False
        VarBind s   -> s `contains` vi
        TyVarBind s -> s `contains` vi
    where
        contains t vi = case t of 
            Arrow t1 t2 -> t1 `contains` vi || t2 `contains` vi
            Concrete _   -> False
            Var vi'     -> vi' == vi

printMetaType :: Show a => Context -> MetaType a -> String
printMetaType ctx t = case t of
    Arrow t1 t2   -> " (" ++ printMetaType ctx t1 ++ " -> " ++ printMetaType ctx t2 ++ ") "
    Var db        -> "(" ++ "TyVar " ++ show db ++ ")"
    Concrete a    -> show a

printType ctx (Type pt ct) = printPrimitiveType pt ++ printTimeType ctx ct 

printPrimitiveType :: PrimitiveType -> String
printPrimitiveType TyBool = "Bool"
printPrimitiveType TyInt  = "Int"

printTimeType ctx (TimeUnbound n i) = 
        "<" ++ (fst $ index2name ctx n) ++ " + " ++ show i ++ ">"

printTimeType ctx (TimeBound i o  ) = "<" ++ (fst $ index2name ctx i) ++ show o ++ ">"
printTimeType ctx (TimeLiteral o  ) = "<" ++ show o ++ ">"

printTerm :: Context -> Term -> String
printTerm ctx t = case t of
    TmAbs x t1      ->  let (ctx',x') = pickFreshName ctx x 
                        in "(lam " ++ x' ++ ". " ++ printTerm ctx' t1 ++ ")"
    TmTAbs x t1     ->  let (ctx',x') = pickFreshName ctx x 
                        in "(lam " ++ x' ++ ". " ++ printTerm ctx' t1 ++ ")"
    TmApp t1 t2     ->  "(" ++ printTerm ctx t1 ++ " " ++ printTerm ctx t2 ++ ")"
    TmVar n         ->  fst $ index2name ctx n
    TmAdd t1 t2     ->  "(" ++ printTerm ctx t1 ++ " + " ++ printTerm ctx t2 ++ ")"
    TmIf t1 t2 t3 
                    ->  "( if (" ++ printTerm ctx t1 ++ ") then (" 
                        ++ printTerm ctx t2 ++ ") else (" 
                        ++ printTerm ctx t3 ++ "))"
    TmAs tm ty      ->  "( " ++ printTerm ctx tm ++ " : " ++ printMetaType ctx ty ++ " )"
    TmLet lb tm     ->  let (ctx',str) = printLetBind ctx lb 
                        in "( let (" ++ str ++ ") in " ++ printTerm ctx' tm ++ ")"
    TmTime t c     ->  printPTerm t ++ printCTerm c

printLetBind ctx []       = (ctx, [])
printLetBind ctx (lb:lbs) =  
    let (ctx',str) = printLetBind' ctx lb 
        (ctx'',str') = printLetBind ctx' lbs
    in  (ctx'',str ++ ", " ++ str')

printLetBind' :: Context -> (String,Term) -> (Context,String)
printLetBind' ctx (str,tm) = 
    let (ctx',tm')  = pickFreshName ctx str
        str'        = tm' ++ " = " ++ printTerm ctx tm
    in  (ctx',str')

printPTerm (TmBool t) = show t
printPTerm (TmInt  t) = show t 

printCTerm (CTmOffset o) = "<" ++ show o ++ ">"

pickFreshName ctx x = pickFreshName' ctx x 0
pickFreshName' ctx x n = 
    case y of 
        Just z  -> pickFreshName' ctx x (n+1)
        Nothing -> (ctx',x')
        where 
            y    = lookup x' ctx
            x'   = x ++ (show n)
            ctx' = (x',NameBind) : ctx

