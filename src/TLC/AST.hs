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
-- Module               : TLC.AST
-- Description          : Strongly-typed abstract syntax for a λ-calculus
-- Copyright            : (c) Galois, Inc.  2017
-- Maintainer           : Robert Dockins <rdockins@galois.com>
--
-- This module defines a strongly-typed abstract syntax for a typed
-- λ-calculus, using a host of fancy GHC extensions (in particular
-- Generalized Algebraic Data Types, GADTs) to directly embed the
-- simple type discipline of λ-terms directly into GHC's type system.
--
-- The major purpose of this module is to demonstrate the techniques
-- required to successfully work in this atmosphere of rich types.
-- Special data structures, generalizations of existing programming
-- patterns and programming techniques are often required; many of
-- these useful patterns and utilites have been captuered in the
-- 'parameterized-utils' package.  This module demonstrates the
-- use of quite a few of these.
-------------------------------------------------------------------
module TLC.AST where

import Data.Functor.Const

import Data.Parameterized.Classes
import Data.Parameterized.Context as Ctx
import Data.Parameterized.TraversableFC

-- | This data declaration is used as a 'DataKind'.
--   It is promoted to a kind, so that the constructors
--   can be used as indices to GADT.
data Type where
  (:->) :: Type -> Type -> Type
  BoolT :: Type
  IntT  :: Type
  (:*:) :: Type -> Type -> Type

infixr 5 :->
infixr 6 :*:

-- | The 'TypeRepr' family is a run-time representation of the
--   data kind 'Type' it allows us to do runtime tests and computation
--   on 'Type'.  The shape of the data constructors exactly mirror
--   the shape of the data kind 'Type'.
data TypeRepr :: Type -> * where
  ArrowRepr :: TypeRepr τ₁ -> TypeRepr τ₂ -> TypeRepr (τ₁ :-> τ₂)
  BoolRepr  :: TypeRepr BoolT
  IntRepr   :: TypeRepr IntT
  PairRepr  :: TypeRepr τ₁ -> TypeRepr τ₂ -> TypeRepr (τ₁ :*: τ₂)

instance Show (TypeRepr τ) where
  showsPrec _ IntRepr  = showString "IntT"
  showsPrec _ BoolRepr = showString "BoolT"
  showsPrec d (ArrowRepr x y) =
     showParen (d > 5) $
       showsPrec 6 x . showString " :-> " . showsPrec 5 y
  showsPrec d (PairRepr x y) =
     showParen (d > 6) $
       showsPrec 7 x . showString " :*: " . showsPrec 6 y

instance ShowF TypeRepr

instance KnownRepr TypeRepr IntT where knownRepr = IntRepr
instance KnownRepr TypeRepr BoolT where knownRepr = BoolRepr
instance (KnownRepr TypeRepr τ₁, KnownRepr TypeRepr τ₂) => KnownRepr TypeRepr (τ₁ :-> τ₂) where
  knownRepr = ArrowRepr knownRepr knownRepr
instance (KnownRepr TypeRepr τ₁, KnownRepr TypeRepr τ₂) => KnownRepr TypeRepr (τ₁ :*: τ₂) where
  knownRepr = PairRepr knownRepr knownRepr

instance TestEquality TypeRepr where
  testEquality BoolRepr BoolRepr = return Refl
  testEquality IntRepr  IntRepr  = return Refl
  testEquality (ArrowRepr x₁ x₂) (ArrowRepr y₁ y₂) =
    do Refl <- testEquality x₁ y₁
       Refl <- testEquality x₂ y₂
       return Refl
  testEquality (PairRepr x₁ x₂) (PairRepr y₁ y₂) =
    do Refl <- testEquality x₁ y₁
       Refl <- testEquality x₂ y₂
       return Refl
  testEquality _ _ = Nothing

-- | This is the main term representation for our STLC.  It is explicitly
--   a representation of "open" terms.  The 'Term' type has two parameters.
--   The first 'γ', is a context that fixes the types of the free variables
--   occuring in the term.  The second 'τ', is the result type of the term.
data Term (γ :: Ctx Type) (τ :: Type) :: * where
  TmVar  :: Index γ τ -> Term γ τ
  TmWeak :: Term γ τ -> Term (γ ::> τ') τ
  TmInt  :: Int -> Term γ IntT
  TmLe   :: Term γ IntT -> Term γ IntT -> Term γ BoolT
  TmAdd  :: Term γ IntT -> Term γ IntT -> Term γ IntT
  TmNeg  :: Term γ IntT -> Term γ IntT
  TmBool :: Bool -> Term γ BoolT
  TmIte  :: Term γ BoolT -> Term γ τ -> Term γ τ -> Term γ τ
  TmPair :: Term γ τ₁ -> Term γ τ₂ -> Term γ (τ₁ :*: τ₂)
  TmFst  :: Term γ (τ₁ :*: τ₂) -> Term γ τ₁
  TmSnd  :: Term γ (τ₁ :*: τ₂) -> Term γ τ₂
  TmApp  :: Term γ (τ₁ :-> τ₂) -> Term γ τ₁ -> Term γ τ₂
  TmAbs  :: String -> TypeRepr τ₁ -> Term (γ ::> τ₁) τ₂ -> Term γ (τ₁ :-> τ₂)
  TmFix  :: String -> TypeRepr τ  -> Term (γ ::> τ)  τ  -> Term γ τ


infixl 5 :@

instance Num (Term γ IntT) where
  fromInteger n = TmInt (fromInteger n)
  x + y = TmAdd x y
  negate (TmInt x) = TmInt (negate x)
  negate x = TmNeg x
  x * y = error "multiplication not defined"
  abs = error "Abs not defined"
  signum = error "signum not defined"

pattern (:@) :: Term γ (τ₁ :-> τ₂) -> Term γ τ₁ -> Term γ τ₂
pattern x :@ y = TmApp x y

-- | A helper function for constructing lambda terms
λ :: KnownRepr TypeRepr τ₁ => String -> Term (γ ::> τ₁) τ₂ -> Term γ (τ₁ :-> τ₂)
λ nm x = TmAbs nm knownRepr x

-- | A helper function for constructing fixpoint terms
μ :: KnownRepr TypeRepr τ => String -> Term (γ ::> τ) τ -> Term γ τ
μ nm x = TmFix nm knownRepr x

-- | A pattern for variables.  This is intended to be used with explicit
--   type applications, e.g. @Var \@2@.
pattern Var :: forall n γ τ. Idx n γ τ => Term γ τ
pattern Var <- TmVar (testEquality (natIndex @n) -> Just Refl)
 where Var = TmVar (natIndex @n)

pattern (:<=) :: Term γ IntT -> Term γ IntT -> Term γ BoolT
pattern x :<= y = TmLe x y

-- | A simple pretty printer for terms.
printTerm :: Assignment (Const (Int -> ShowS)) γ
          -> Int
          -> Term γ τ
          -> ShowS
printTerm pvar prec tm = case tm of
  TmVar i -> getConst (pvar!i) prec
  TmWeak x -> printTerm (Ctx.init pvar) prec x
  TmInt n -> shows n
  TmBool b -> shows b
  TmLe x y -> showParen (prec > 6) (printTerm pvar 7 x . showString " <= " . printTerm pvar 7 y)
  TmAdd x y -> showParen (prec > 5) (printTerm pvar 6 x . showString " + " . printTerm pvar 6 y)
  TmNeg x -> showParen (prec > 10) (showString "negate " . printTerm pvar 11 x)
  TmIte c x y -> showParen (prec > 3) $
                 showString "if " . printTerm pvar 0 c .
                 showString " then " . printTerm pvar 4 x .
                 showString " else " . printTerm pvar 4 y
  TmPair x y -> showParen True $
                  printTerm pvar 0 x .
                  showString ", " .
                  printTerm pvar 0 y
  TmFst x -> showParen (prec > 10) $ showString "fst " . printTerm pvar 11 x
  TmSnd x -> showParen (prec > 10) $ showString "snd " . printTerm pvar 11 x
  TmApp x y -> showParen (prec > 10) (printTerm pvar 10 x) . showString " " . printTerm pvar 11 y
  TmFix nm tp x ->
    let nm' = if Prelude.null nm then "v" else nm
        vnm _prec = showString nm' . shows (sizeInt (size pvar)) in
    showParen (prec > 0) $
      showString "μ " . vnm 0 .
      showString " : " . showsPrec 0 tp .
      showString ". " . printTerm (pvar :> Const vnm) 0 x
  TmAbs nm tp x ->
    let nm' = if Prelude.null nm then "v" else nm
        vnm _prec = showString nm' . shows (sizeInt (size pvar)) in
    showParen (prec > 0) $
      showString "λ " . vnm 0 .
      showString " : " . showsPrec 0 tp .
      showString ". " . printTerm (pvar :> Const vnm) 0 x

instance KnownContext γ => Show (Term γ τ) where
  showsPrec = printTerm (generate knownSize (\i -> Const (\_ -> shows (indexVal i))))


-- | Given an assignment of (run-time) types for the free variables, compute the
--   (run-time) type of a term.
computeType ::
  Assignment TypeRepr γ ->
  Term γ τ ->
  TypeRepr τ
computeType env tm = case tm of
  TmVar i -> env!i
  TmWeak x -> computeType (Ctx.init env) x
  TmInt _ -> IntRepr
  TmBool _ -> BoolRepr
  TmLe _ _ -> BoolRepr
  TmAdd _ _ -> IntRepr
  TmNeg _ -> IntRepr
  TmIte _ x _ -> computeType env x
  TmPair x y -> PairRepr (computeType env x) (computeType env y)
  TmFst x ->
    case computeType env x of PairRepr τ _ -> τ
  TmSnd x ->
    case computeType env x of PairRepr _ τ -> τ
  TmApp x y ->
    case computeType env x of ArrowRepr _ τ -> τ
  TmAbs _ τ₁ x ->
    let τ₂ = computeType (env :> τ₁) x in ArrowRepr τ₁ τ₂
  TmFix _ τ _ -> τ

-- | A generic representation of values.  A value for this calculus
--   is either a basic value of one of the base types (Int or Bool)
--   or a lambda abstraction.  Values for lambda abstractions consist
--   of a closure and a term body.
--
--   The sorts of values contained in the
--   closure are controlled by the type parameter @f@; this varies depending
--   on the evaluation strategy.
data Value (f :: Type -> *) (τ :: Type) :: * where
  VInt   :: Int -> Value f IntT
  VBool  :: Bool -> Value f BoolT
  VAbs   :: Assignment f γ -> TypeRepr τ₁ -> Term (γ ::> τ₁) τ₂ -> Value f (τ₁ :-> τ₂)
  VPair  :: f τ₁ -> f τ₂ -> Value f (τ₁ :*: τ₂)

instance ShowFC Value where
  showsPrecFC _sh _prec (VInt n) = shows n
  showsPrecFC _sh _prec (VBool b) = shows b
  showsPrecFC sh prec (VAbs env τ tm) =
     printTerm (fmapFC (\x -> Const (\p -> sh p x)) env) prec (TmAbs [] τ tm)
  showsPrecFC sh prec (VPair _x _y) = showString "<pair>"

instance ShowF f => ShowF (Value f)
instance ShowF f => Show (Value f τ) where
  show = showFC showF
