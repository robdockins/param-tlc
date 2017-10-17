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
import Data.Monoid

import Data.Parameterized.Classes
import Data.Parameterized.Context hiding ((++))
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

instance ShowF TypeRepr where
  showF IntRepr = "IntT"
  showF BoolRepr = "BoolT"
  showF (ArrowRepr x y) = showF x <+> ":->" <+> "(" <> showF y <> ")"

instance Show (TypeRepr τ) where
  show = showF

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

(<+>) :: String -> String -> String
x <+> y = x <> " " <> y

printTerm :: Assignment (Const String) γ
          -> Term γ τ
          -> String
printTerm pvar tm = case tm of
  TmVar i -> getConst (pvar!i)
  TmInt n -> show n
  TmBool b -> show b
  TmLe x y -> "(" <> printTerm pvar x <+> "<=" <+> printTerm pvar y <> ")"
  TmAdd x y -> "(" <> printTerm pvar x <+> "+" <+> printTerm pvar y <> ")"
  TmNeg x -> "(negate" <+> printTerm pvar x <> ")"
  TmIte c x y -> "if" <+> printTerm pvar c <+>
                   "then" <+> printTerm pvar x <+> "else" <+> printTerm pvar y
  TmApp x y -> "(" <> printTerm pvar x <> ")" <+> printTerm pvar y 
  TmFix _ x ->
    let vnm = "v" ++ show (sizeInt (size pvar)) in
    "μ" <> vnm <> "." <+> printTerm (pvar :> Const vnm) x
  TmAbs _ x ->
    let vnm = "v" ++ show (sizeInt (size pvar)) in
    "λ" <> vnm <> "." <+> printTerm (pvar :> Const vnm) x

instance KnownContext γ => Show (Term γ τ) where
  show = printTerm (generate knownSize (Const . show . indexVal))


computeType ::
  Assignment TypeRepr γ ->
  Term γ τ ->
  TypeRepr τ
computeType env tm = case tm of
  TmVar i -> env!i
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
  showFC sh (VInt n) = show n
  showFC sh (VBool b) = show b
  showFC sh (VAbs env τ tm) = printTerm (fmapFC (Const . sh) env) (TmAbs τ tm)
instance ShowF f => ShowF (Value f) where
  showF = showFC showF
instance ShowF f => Show (Value f τ) where
  show = showF
