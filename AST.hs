{-# LANGUAGE TypeSynonymInstances, FlexibleInstances #-}
module AST 
    where

import Control.Applicative
import Data.SBV

data Context = Context 
             { timeVarBind  :: [TimeVarBinding]
             , typeVarBind  :: [TypeVarBinding]
             , schemeBind   :: [SchemeBinding]
             }

type LetBind    = [(String,Term)]
type AtUnbound  = [(UnboundedTime,Term)]
type AtBound    = [(BoundedTime,Term)]

type TimeVarBinding = (String,MetaType BoundedType)
type TypeVarBinding = (String,MetaType BoundedType)
type SchemeBinding  = (String,MetaType BoundedType)

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

data Term = TmTypeVar DeBruijn 
          | TmSchemeVar DeBruijn
          | TmTimeVar DeBruijn
          | TmAbs String Term
          | TmTAbs String Term
          | TmApp Term Term  
          | TmAs Term (MetaType UnboundedType)
          | TmAdd Term Term
          | TmIf Term Term Term
          | TmLet LetBind Term
          | TmAt TmAt
          | TmTime PrimitiveTerm TimeTerm
          | TmReset
          | TmClock
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

ctx2TypeScheme :: Context -> DeBruijn -> MetaType BoundedType
ctx2TypeScheme ctx db = 
    let (_,bind) = index2name (schemeBind ctx) db
    in  bind

ctx2TypeVar :: Context -> DeBruijn -> MetaType BoundedType
ctx2TypeVar ctx db = 
    let (_,bind) = index2name (typeVarBind ctx) db
    in  bind

ctx2TimeVar :: Context -> DeBruijn -> MetaType BoundedType
ctx2TimeVar ctx db = 
    let (_,bind) = index2name (timeVarBind ctx) db
    in  bind

index2name xs l | length xs >= l = xs !! l
                | otherwise      = error $ show xs ++ " with index " ++ show l


isInContext :: VariableIndex -> [(String,MetaType BoundedType)] -> Bool
isInContext vi = let f (_,bind) = bind `contains` vi
                 in foldl (||) True . map f
    where
        contains t vi = case t of 
            Arrow t1 t2 -> t1 `contains` vi || t2 `contains` vi
            Constant _  -> False
            Var vi'     -> vi' == vi

