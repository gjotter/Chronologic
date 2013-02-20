{-# LANGUAGE TypeSynonymInstances, FlexibleInstances #-}
module AST 
    where

import Control.Applicative
import Data.SBV

type Context = [(String,Binding)]
type LetBind = [(String,Term)]
type AtUnbound  = [(UnboundedTime,Term)]
type AtBound    = [(BoundedTime,Term)]

data Binding = NameBind
             | VarBind (MetaType BoundedType)
             | TyVarBind (MetaType BoundedType)
             | TyScheme (MetaType BoundedType)
             deriving Show

data MetaType a = Arrow (MetaType a) (MetaType a)
                | Var VariableIndex
                | Constant a
                deriving (Eq,Show)

data BoundedType = BoundedType PrimitiveType BoundedTime
          deriving (Eq,Show)

data UnboundedType = UnboundedType PrimitiveType UnboundedTime
          deriving (Eq,Show)

data PrimitiveType 
    = TyBool 
    | TyInt
    deriving (Eq,Show)

data BoundedTime
    = BoundedTime TimeVariableIndex Offset
    | TimeLiteral Offset
    deriving (Show, Eq)

data UnboundedTime = UnboundedTime DeBruijn Offset
                 deriving (Eq,Show)

type TimeVariableIndex = Int
type VariableIndex = Int
type DeBruijn = Int
type Offset = SInteger

data Term = TmVar DeBruijn 
          | TmAbs String Term
          | TmTAbs String Term
          | TmApp Term Term  
          | TmAs Term (MetaType UnboundedType)
          | TmAdd Term Term
          | TmIf Term Term Term
          | TmLet LetBind Term
          | TmAt TmAt
          | TmTime PrimitiveTerm TimeTerm
          deriving (Eq,Show)

data TmAt = TmAtBound AtBound
          | TmAtUnbound AtUnbound
          deriving (Eq, Show)

data PrimitiveTerm = TmBool Bool
                   | TmInt Int
                   deriving (Eq,Show)

data TimeTerm = TmOffset Offset
    deriving (Eq,Show)

mapTyC :: (BoundedTime -> BoundedTime) -> MetaType BoundedType -> MetaType BoundedType
mapTyC f t =
    case t of
        Arrow t1 t2                -> Arrow (f `mapTyC` t1) (f `mapTyC` t2)
        Constant (BoundedType pt tt) -> Constant $ BoundedType pt (f tt)
        Var v                      -> Var v

emptyContext = []

ctx2Type :: Context -> DeBruijn -> MetaType BoundedType
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

