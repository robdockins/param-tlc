{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}

{-# OPTIONS_GHC -Werror #-}
{-# OPTIONS -Wincomplete-patterns #-}
{-# OPTIONS -Wunused-imports #-}
----------------------------------------------------------------
-- |
-- Module               : TLC.SimpleTerm
-- Description          : Strongly-typed abstract syntax
--                         a simple term language
-- Copyright            : (c) Galois, Inc.  2018
-- Maintainter          : Robert Dockins <rdockins@galois.com>
--
-- This module defines a simple first-order term syntax operating
-- on booleans an integers to introduce the main ideas of
-- GADTs, data kinds, type representatives, and typed evaluation.
-------------------------------------------------------------------

module TLC.SimpleTerm where

import Data.Parameterized.Classes

-- | This data declaration is used as a 'DataKind'.
--   It is promoted to a kind, so that the constructors
--   can be used as indices to GADT.
data Type = BoolT | IntT

-- | The 'TypeRepr' family is a run-time representation of the
--   data kind 'Type' it allows us to do runtime tests and computation
--   on 'Type'.  The shape of the data constructors exactly mirror
--   the shape of the data kind 'Type'.
data TypeRepr :: Type -> * where
  BoolRepr  :: TypeRepr BoolT
  IntRepr   :: TypeRepr IntT


instance Show (TypeRepr τ) where
  showsPrec _ IntRepr  = showString "IntT"
  showsPrec _ BoolRepr = showString "BoolT"

instance ShowF TypeRepr

instance KnownRepr TypeRepr IntT where knownRepr = IntRepr
instance KnownRepr TypeRepr BoolT where knownRepr = BoolRepr

instance TestEquality TypeRepr where
  testEquality BoolRepr BoolRepr = return Refl
  testEquality IntRepr  IntRepr  = return Refl
  testEquality _ _ = Nothing


-- | This is the main term represntation for our simple calculator language.
--   The parameter 'τ' is the result type of the term.
data Term (τ :: Type) :: * where
  TmInt  :: Int -> Term IntT
  TmLe   :: Term IntT -> Term IntT -> Term BoolT
  TmAdd  :: Term IntT -> Term IntT -> Term IntT
  TmNeg  :: Term IntT -> Term IntT
  TmBool :: Bool -> Term BoolT
  TmIte  :: forall α. Term BoolT -> Term α -> Term α -> Term α

-- | A simple pretty printer for terms.
printTerm :: Int
          -> Term τ
          -> ShowS
printTerm prec tm = case tm of
  TmInt n -> shows n
  TmBool b -> shows b
  TmLe x y -> showParen (prec > 6) (printTerm 7 x . showString " <= " . printTerm 7 y)
  TmAdd x y -> showParen (prec > 5) (printTerm 6 x . showString " + " . printTerm 6 y)
  TmNeg x -> showParen (prec > 10) (showString "negate " . printTerm 11 x)
  TmIte c x y -> showParen (prec > 3) $
                 showString "if " . printTerm 0 c .
                 showString " then " . printTerm 4 x .
                 showString " else " . printTerm 4 y


-- | Compute the (run-time) type of a term.
computeType :: Term τ -> TypeRepr τ
computeType tm = case tm of
  TmInt _ -> IntRepr
  TmBool _ -> BoolRepr
  TmLe _ _ -> BoolRepr
  TmAdd _ _ -> IntRepr
  TmNeg _ -> IntRepr
  TmIte _ x _ -> computeType x


-- | A generic representation of values.  A value for this calculus
--   is either a basic value of one of the base types (Int or Bool).
data Value (τ :: Type) :: * where
  VInt   :: Int -> Value IntT
  VBool  :: Bool -> Value BoolT

instance ShowF Value
instance Show (Value τ) where
  show (VInt i) = show i
  show (VBool b) = show b



-- | Reduce a term expression to a value
eval :: Term τ -> Value τ
eval tm = case tm of
   TmBool b -> VBool b
   TmInt n  -> VInt n
   TmLe x y ->
     case (eval x, eval y) of
       -- NB! GHC knows that this is the only possibility!
       (VInt a, VInt b) -> VBool $! a <= b
   TmAdd x y ->
     case (eval x, eval y) of
       (VInt a, VInt b) -> VInt $! a + b
   TmNeg x ->
      case eval x of
        VInt a -> VInt $! negate a
   TmIte c x y ->
     case eval c of
       VBool True  -> eval x
       VBool False -> eval y
