{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}

{-# OPTIONS_GHC -Werror #-}
{-# OPTIONS -Wincomplete-patterns #-}
{-# OPTIONS -Wunused-imports #-}

module TLC.AST where

import Data.Functor.Const

import Data.Parameterized.Classes
import Data.Parameterized.Context as Ctx hiding ((++))
import Data.Parameterized.TraversableFC

data Type where
  (:->) :: Type -> Type -> Type
  BoolT :: Type
  IntT  :: Type

infixr 5 :->

data TypeRepr :: Type -> * where
  ArrowRepr :: TypeRepr τ₁ -> TypeRepr τ₂ -> TypeRepr (τ₁ :-> τ₂)
  BoolRepr  :: TypeRepr BoolT
  IntRepr   :: TypeRepr IntT

instance Show (TypeRepr τ) where
  showsPrec _ IntRepr  = showString "IntT"
  showsPrec _ BoolRepr = showString "BoolT"
  showsPrec d (ArrowRepr x y) =
     showParen (d > 5) $
       showsPrec 6 x . showString " :-> " . showsPrec 5 y

instance ShowF TypeRepr

instance KnownRepr TypeRepr IntT where knownRepr = IntRepr
instance KnownRepr TypeRepr BoolT where knownRepr = BoolRepr
instance (KnownRepr TypeRepr τ₁, KnownRepr TypeRepr τ₂) => KnownRepr TypeRepr (τ₁ :-> τ₂) where
  knownRepr = ArrowRepr knownRepr knownRepr

instance TestEquality TypeRepr where
  testEquality BoolRepr BoolRepr = return Refl
  testEquality IntRepr  IntRepr  = return Refl
  testEquality (ArrowRepr x₁ x₂) (ArrowRepr y₁ y₂) =
    do Refl <- testEquality x₁ y₁
       Refl <- testEquality x₂ y₂
       return Refl
  testEquality _ _ = Nothing

data Term (γ :: Ctx Type) (τ :: Type) :: * where
  TmVar  :: Index γ τ -> Term γ τ
  TmWeak :: Term γ τ -> Term (γ ::> τ') τ
  TmInt  :: Int -> Term γ IntT
  TmLe   :: Term γ IntT -> Term γ IntT -> Term γ BoolT
  TmAdd  :: Term γ IntT -> Term γ IntT -> Term γ IntT
  TmNeg  :: Term γ IntT -> Term γ IntT
  TmBool :: Bool -> Term γ BoolT
  TmIte  :: Term γ BoolT -> Term γ τ -> Term γ τ -> Term γ τ
  TmApp  :: Term γ (τ₁ :-> τ₂) -> Term γ τ₁ -> Term γ τ₂
  TmAbs  :: TypeRepr τ₁ -> Term (γ ::> τ₁) τ₂ -> Term γ (τ₁ :-> τ₂)
  TmFix  :: TypeRepr τ  -> Term (γ ::> τ)  τ  -> Term γ τ

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

λ :: KnownRepr TypeRepr τ₁ => Term (γ ::> τ₁) τ₂ -> Term γ (τ₁ :-> τ₂)
λ x = TmAbs knownRepr x

μ :: KnownRepr TypeRepr τ => Term (γ ::> τ) τ -> Term γ τ
μ x = TmFix knownRepr x

pattern Var :: forall n γ τ. Idx n γ τ => Term γ τ
pattern Var <- TmVar (testEquality (natIndex @n) -> Just Refl)
 where Var = TmVar (natIndex @n)

pattern (:<=) :: Term γ IntT -> Term γ IntT -> Term γ BoolT
pattern x :<= y = TmLe x y

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
  TmApp x y -> showParen (prec > 10) (printTerm pvar 10 x) . showString " " . printTerm pvar 11 y
  TmFix tp x ->
    let vnm _prec = showString "v" . shows (sizeInt (size pvar)) in
    showParen (prec > 0) $
      showString "μ" . vnm 0 .
      showString " : " . showsPrec 0 tp .
      showString ". " . printTerm (pvar :> Const vnm) 0 x
  TmAbs tp x ->
    let vnm _prec = showString "v" . shows (sizeInt (size pvar)) in
    showParen (prec > 0) $
      showString "λ" . vnm 0 .
      showString " : " . showsPrec 0 tp .
      showString ". " . printTerm (pvar :> Const vnm) 0 x

instance KnownContext γ => Show (Term γ τ) where
  showsPrec = printTerm (generate knownSize (\i -> Const (\_ -> shows (indexVal i))))


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
  TmApp x y ->
    case computeType env x of ArrowRepr _ τ -> τ
  TmAbs τ₁ x ->
    let τ₂ = computeType (env :> τ₁) x in ArrowRepr τ₁ τ₂
  TmFix τ _ -> τ


data Value (f :: Type -> *) (τ :: Type) :: * where
  VInt   :: Int -> Value f IntT
  VBool  :: Bool -> Value f BoolT
  VAbs   :: Assignment f γ -> TypeRepr τ₁ -> Term (γ ::> τ₁) τ₂ -> Value f (τ₁ :-> τ₂)

instance ShowFC Value where
  showsPrecFC _sh _prec (VInt n) = shows n
  showsPrecFC _sh _prec (VBool b) = shows b
  showsPrecFC sh prec (VAbs env τ tm) =
     printTerm (fmapFC (\x -> Const (\p -> sh p x)) env) prec (TmAbs τ tm)
instance ShowF f => ShowF (Value f)
instance ShowF f => Show (Value f τ) where
  show = showFC showF
