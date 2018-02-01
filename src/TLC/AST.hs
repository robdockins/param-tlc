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
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns #-}

{-# OPTIONS_GHC -Werror #-}
{-# OPTIONS -Wincomplete-patterns #-}
{-# OPTIONS -Wunused-imports #-}
----------------------------------------------------------------
-- |
-- Module               : TLC.AST
-- Copyright            : (c) Galois, Inc.  2017
-- Maintainter          : Robert Dockins <rdockins@galois.com>
-- Synopsis             : Strongly-typed sbstract syntax for a λ-calculus
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

import qualified Data.Kind as Haskell
import           Data.Type.Equality

import Data.Functor.Const

import Data.Parameterized.Classes
import Data.Parameterized.Context as Ctx
import Data.Parameterized.TraversableFC

data Kind where
  (:=>) :: Kind -> Kind -> Kind
  Star  :: Kind

infixr 5 :=>

data KindRepr :: Kind -> Haskell.Type where
  KArrowRepr :: KindRepr k₁ -> KindRepr k₂ -> KindRepr (k₁ :=> k₂)
  StarRepr   :: KindRepr Star

instance Show (KindRepr k) where
  showsPrec _ StarRepr = showString "*"
  showsPrec d (KArrowRepr k₁ k₂) =
    showParen (d > 5) $
      showsPrec 6 k₁ . showString " :=> " . showsPrec 5 k₂
instance ShowF KindRepr

instance KnownRepr KindRepr Star where
  knownRepr = StarRepr
instance (KnownRepr KindRepr k₁, KnownRepr KindRepr k₂) => KnownRepr KindRepr (k₁ :=> k₂) where
  knownRepr = KArrowRepr knownRepr knownRepr
instance TestEquality KindRepr where
  testEquality StarRepr StarRepr = return Refl
  testEquality (KArrowRepr x₁ x₂) (KArrowRepr y₁ y₂) =
    do Refl <- testEquality x₁ y₁
       Refl <- testEquality x₂ y₂
       return Refl
  testEquality _ _ = Nothing

-- | This data declaration is used as a 'DataKind'.
--   It is promoted to a kind, so that the constructors
--   can be used as indices to GADT.
data Type :: Ctx Kind -> Kind -> Haskell.Type where
  VarT    :: Type (δ ::> k) k
  WeakT   :: Type δ k -> Type (δ ::> k') k
  AllT    :: Type (δ ::> k') k -> Type δ k
  ArrowT  :: Type δ (Star :=> Star :=> Star)
  BoolT   :: Type δ Star
  IntT    :: Type δ Star
  (:@@)   :: Type δ (k₁ :=> k₂) -> Type δ k₁ -> Type δ k₂

infixl 4 :@@
infixr 5 :->

type (:->) x y = ArrowT :@@ x :@@ y

type family WkCtx (γ :: Ctx (Type δ k)) :: Ctx (Type (δ ::> k') k) where
  WkCtx EmptyCtx  = EmptyCtx
  WkCtx (γ ::> τ) = WkCtx γ ::> WeakT τ


data TySubst (δ :: Ctx Kind) (δ' :: Ctx Kind) where
  TySubstId   :: TySubst δ δ'
  TySubstLift :: TySubst δ δ' -> TySubst (δ ::> k) (δ' ::> k)
  TySubstCons :: TySubst δ δ' -> Type δ' k -> TySubst (δ ::> k) δ'


type family SubstTAssign (assn :: TySubst δ δ') (t :: Type δ k) :: Type δ' k where
  SubstTAssign TySubstId x = x

  SubstTAssign (TySubstLift sub)    VarT = VarT
  SubstTAssign (TySubstCons sub t)  VarT = t

  SubstTAssign (TySubstLift sub)    (WeakT x) = WeakT (SubstTAssign sub x)
  SubstTAssign (TySubstCons sub t)  (WeakT x) = SubstTAssign sub x

  SubstTAssign sub (AllT x)  = AllT (SubstTAssign (TySubstLift sub) x)
  SubstTAssign sub (x :@@ y) = SubstTAssign sub x :@@ SubstTAssign sub y
  SubstTAssign sub ArrowT    = ArrowT
  SubstTAssign sub BoolT     = BoolT
  SubstTAssign sub IntT      = IntT

type SubstT (f :: Type (δ ::> k') k) (t :: Type δ k') =
  SubstTAssign (TySubstCons TySubstId t) f

type family SubstTCtx (ctx :: Ctx (Type (δ ::> k') k)) (t :: Type δ k') :: Ctx (Type δ k) where
  SubstTCtx EmptyCtx t = EmptyCtx
  SubstTCtx (ctx ::> f) t = SubstTCtx ctx t ::> SubstT f t

-- | The 'TypeRepr' family is a run-time representation of the
--   data kind 'Type' it allows us to do runtime tests and computation
--   on 'Type'.  The shape of the data constructors exactly mirror
--   the shape of the data kind 'Type'.
data TypeRepr (δ :: Ctx Kind) (k :: Kind) :: Type δ k -> Haskell.Type where
  VarTRepr  :: TypeRepr (γ ::> k) k VarT
  WeakTRepr :: TypeRepr δ k t -> TypeRepr (δ ::> k') k (WeakT t)
  AllTRepr  :: KindRepr k' -> TypeRepr (δ ::> k') k t -> TypeRepr δ k (AllT t)
  ArrRepr   :: TypeRepr δ (Star :=> Star :=> Star) ArrowT
  BoolRepr  :: TypeRepr δ Star BoolT
  IntRepr   :: TypeRepr δ Star IntT
  AppRepr   :: forall δ k₁ k₂ t₁ t₂.
                  KindRepr k₁ ->
                  TypeRepr δ (k₁ :=> k₂) t₁ ->
                  TypeRepr δ k₁ t₂ ->
                  TypeRepr δ k₂ (t₁ :@@ t₂)

pattern ArrowRepr ::
  () => (k ~ Star, t ~~ (t₁ :-> t₂)) =>
  TypeRepr δ Star t₁ -> TypeRepr δ Star t₂ -> TypeRepr δ k t
pattern ArrowRepr t₁ t₂ = AppRepr StarRepr (AppRepr StarRepr ArrRepr t₁) t₂


instance Show (TypeRepr δ k τ) where
  showsPrec d (ArrowRepr x y) =
     showParen (d > 5) $
       showsPrec 6 x . showString " :-> " . showsPrec 5 y

  showsPrec _ VarTRepr = showString "VAR"
  showsPrec d (WeakTRepr t) =
     showParen (d > 10) $
       showString "W " . showsPrec 11 t
  showsPrec d (AllTRepr k t) =
     showParen (d > 0) $
       showString "∀" . showsPrec 0 k . showString ". " .
       showsPrec 0 t
  showsPrec _ IntRepr  = showString "IntT"
  showsPrec _ BoolRepr = showString "BoolT"
  showsPrec _ ArrRepr  = showString "(:->)"
  showsPrec d (AppRepr _ x y) =
    showParen (d > 4) $
      showsPrec 4 x . showString " :@@ " . showsPrec 5 y


instance ShowF (TypeRepr δ k)

instance KnownRepr (TypeRepr δ Star) IntT where knownRepr = IntRepr
instance KnownRepr (TypeRepr δ Star) BoolT where knownRepr = BoolRepr
instance KnownRepr (TypeRepr δ (Star :=> Star :=> Star)) ArrowT where knownRepr = ArrRepr
instance (KnownRepr KindRepr k₁,
          KnownRepr (TypeRepr δ (k₁ :=> k₂)) t₁,
          KnownRepr (TypeRepr δ k₁) t₂) =>
         KnownRepr (TypeRepr δ k₂) (t₁ :@@ t₂) where
  knownRepr = AppRepr knownRepr knownRepr knownRepr

instance TestEquality (TypeRepr δ k) where
  testEquality BoolRepr BoolRepr = return Refl
  testEquality IntRepr  IntRepr  = return Refl
  testEquality ArrRepr  ArrRepr  = return Refl
  testEquality (AppRepr kx x₁ x₂) (AppRepr ky y₁ y₂) =
    do Refl <- testEquality kx ky
       Refl <- testEquality x₁ y₁
       Refl <- testEquality x₂ y₂
       return Refl
  testEquality _ _ = Nothing

-- | This is the main term representation for our STLC.  It is explicitly
--   a representation of "open" terms.  The 'Term' type has two parameters.
--   The first 'γ', is a context that fixes the types of the free variables
--   occuring in the term.  The second 'τ', is the result type of the term.
data Term (δ :: Ctx Kind) (γ :: Ctx (Type δ Star)) (τ :: Type δ Star) :: Haskell.Type where
  TmVar  :: Index γ τ -> Term δ γ τ
  TmWeak :: Term δ γ τ -> Term δ (γ ::> τ') τ
  TmInt  :: Int -> Term δ γ IntT
  TmLe   :: Term δ γ IntT -> Term δ γ IntT -> Term δ γ BoolT
  TmAdd  :: Term δ γ IntT -> Term δ γ IntT -> Term δ γ IntT
  TmNeg  :: Term δ γ IntT -> Term δ γ IntT
  TmBool :: Bool -> Term δ γ BoolT
  TmIte  :: Term δ γ BoolT -> Term δ γ τ -> Term δ γ τ -> Term δ γ τ
  TmApp  :: Term δ γ (τ₁ :-> τ₂) -> Term δ γ τ₁ -> Term δ γ τ₂
  TmAbs  :: String -> TypeRepr δ Star τ₁ -> Term δ (γ ::> τ₁) τ₂ -> Term δ γ (τ₁ :-> τ₂)
  TmFix  :: String -> TypeRepr δ Star τ  -> Term δ (γ ::> τ)  τ  -> Term δ γ τ

--  TmTAbs :: KindRepr k -> Term (δ ::> k) (WkCtx γ) τ -> Term δ γ (AllT τ)
--  TmTApp :: Term δ γ (AllT f) -> TypeRepr δ k t -> Term δ γ (SubstT f t)

infixl 5 :@

instance Num (Term δ γ IntT) where
  fromInteger n = TmInt (fromInteger n)
  x + y = TmAdd x y
  negate (TmInt x) = TmInt (negate x)
  negate x = TmNeg x
  x * y = error "multiplication not defined"
  abs = error "Abs not defined"
  signum = error "signum not defined"

pattern (:@) :: Term δ γ (τ₁ :-> τ₂) -> Term δ γ τ₁ -> Term δ γ τ₂
pattern x :@ y = TmApp x y

-- | A helper function for constructing lambda terms
λ :: KnownRepr (TypeRepr δ Star) τ₁ => String -> Term δ (γ ::> τ₁) τ₂ -> Term δ γ (τ₁ :-> τ₂)
λ nm x = TmAbs nm knownRepr x

-- | A helper function for constructing fixpoint terms
μ :: KnownRepr (TypeRepr δ Star) τ => String -> Term δ (γ ::> τ) τ -> Term δ γ τ
μ nm x = TmFix nm knownRepr x

-- | A pattern for variables.  This is intended to be used with explicit
--   type applications, e.g. @Var \@2@.
pattern Var :: forall n δ γ τ. Idx n γ τ => Term δ γ τ
pattern Var <- TmVar (testEquality (natIndex @n) -> Just Refl)
 where Var = TmVar (natIndex @n)

pattern (:<=) :: Term δ γ IntT -> Term δ γ IntT -> Term δ γ BoolT
pattern x :<= y = TmLe x y

-- | A simple pretty printer for terms.
printTerm :: Assignment (Const (Int -> ShowS)) γ
          -> Int
          -> Term δ γ τ
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

  -- TmTAbs k x ->
  --   showParen (prec > 0) $
  --     showString "Λ " .
  --     showsPrec 0 k .
  --     showString ". " .
  --     printTerm undefined {-FIXME! pvar -} 0 x

instance KnownContext γ => Show (Term δ γ τ) where
  showsPrec = printTerm (generate knownSize (\i -> Const (\_ -> shows (indexVal i))))


-- | Given an assignment of (run-time) types for the free variables, compute the
--   (run-time) type of a term.
computeType ::
  Assignment (TypeRepr δ Star) γ ->
  Term δ γ τ ->
  TypeRepr δ Star τ
computeType env tm = case tm of
  TmVar i -> env!i
  TmWeak x -> computeType (Ctx.init env) x
  TmInt _ -> IntRepr
  TmBool _ -> BoolRepr
  TmLe _ _ -> BoolRepr
  TmAdd _ _ -> IntRepr
  TmNeg _ -> IntRepr
  TmIte _ x _ -> computeType env x
  TmApp x y ->
    case computeType env x of AppRepr StarRepr (AppRepr StarRepr ArrRepr _) τ -> τ
  TmAbs _ τ₁ x ->
    let τ₂ = computeType (env :> τ₁) x in AppRepr StarRepr (AppRepr StarRepr ArrRepr τ₁) τ₂
  TmFix _ τ _ -> τ
  -- TmTAbs k x -> AllTRepr k (computeType undefined {-FIXME!-} x)


-- | A generic representation of values.  A value for this calculus
--   is either a basic value of one of the base types (Int or Bool)
--   or a lambda abstraction.  Values for lambda abstractions consist
--   of a closure and a term body.
--
--   The sorts of values contained in the
--   closure are controlled by the type parameter @f@; this varies depending
--   on the evaluation strategy.
data Value (f :: Type EmptyCtx Star -> Haskell.Type) (τ :: Type EmptyCtx Star) :: Haskell.Type where
  VInt   :: Int -> Value f IntT
  VBool  :: Bool -> Value f BoolT
  VAbs   :: Assignment f γ -> TypeRepr EmptyCtx Star τ₁ -> Term EmptyCtx (γ ::> τ₁) τ₂ -> Value f (τ₁ :-> τ₂)

instance ShowFC Value where
  showsPrecFC _sh _prec (VInt n) = shows n
  showsPrecFC _sh _prec (VBool b) = shows b
  showsPrecFC sh prec (VAbs env τ tm) =
     printTerm (fmapFC (\x -> Const (\p -> sh p x)) env) prec (TmAbs [] τ tm)
instance ShowF f => ShowF (Value f)
instance ShowF f => Show (Value f τ) where
  show = showFC showF
