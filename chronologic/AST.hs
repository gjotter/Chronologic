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
                | Constant a
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
          | TmTime PrimitiveTerm TimeTerm
          deriving (Eq,Show)

data PrimitiveTerm = TmBool Bool
                   | TmInt Int
                   deriving (Eq,Show)

data TimeTerm = TmOffset Offset
    deriving (Eq,Show)

mapTyC :: (TimeType -> TimeType) -> MetaType Type -> MetaType Type
mapTyC f t =
    case t of
        Arrow t1 t2           -> Arrow (f `mapTyC` t1) (f `mapTyC` t2)
        Constant (Type pt tt) -> Constant $ Type pt (f tt)
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
            Constant _   -> False
            Var vi'     -> vi' == vi

