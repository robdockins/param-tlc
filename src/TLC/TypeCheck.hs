{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}

{-# OPTIONS_GHC -Werror #-}
{-# OPTIONS -Wincomplete-patterns #-}
{-# OPTIONS -Wunused-imports #-}

----------------------------------------------------------------
-- |
-- Module               : TLC.TypeCheck
-- Copyright            : (c) Galois, Inc.  2017
-- Maintainter          : Robert Dockins <rdockins@galois.com>
-- Synopsis             : Typechecking to produce strongly-typed STLC
--
-- This module defines an untyped AST for the STLC and demonstrates
-- how to use runtime type representations to do computations on
-- types sufficent to convince GHC that we can produce a strongly-typed
-- term from untyped input data.
-------------------------------------------------------------------

module TLC.TypeCheck where

import Control.Monad.Except

import Data.List
import Data.Type.Equality

import Data.Parameterized.Context
import Data.Parameterized.Some

import qualified TLC.AST as AST

-- | An untyped term AST that closed follows the strongly-typed
--   AST from "TLC.AST", but has no GADT information.
--
--   To produce well-typed terms we must check a candidate term
--   to ensure it follows proper scope and typing rules.
data Term where
  TmVar  :: String -> Term
  TmInt  :: Int -> Term
  TmBool :: Bool -> Term
  TmLe   :: Term -> Term -> Term
  TmAdd  :: Term -> Term -> Term
  TmNeg  :: Term -> Term
  TmIte  :: Term -> Term -> Term -> Term
  TmApp  :: Term -> Term -> Term
  TmAbs  :: String -> Type -> Term -> Term
  TmFix  :: String -> Type -> Term -> Term
 deriving (Show, Read, Eq, Ord)

data Type where
  IntT :: Type
  BoolT :: Type
  ArrowT :: Type -> Type -> Type
 deriving (Show, Read, Eq, Ord)

typeToRepr ::
  Type ->
  Some AST.TypeRepr
typeToRepr IntT = Some AST.IntRepr
typeToRepr BoolT = Some AST.BoolRepr
typeToRepr (ArrowT x y) =
  case (typeToRepr x, typeToRepr y) of
    (Some x', Some y') -> Some (AST.ArrowRepr x' y')

-- | The result of a typechecking operation in the context
--   of free variable context @γ@ is a type repr and
--   a term of that type.
data TCResult (γ :: Ctx AST.Type) where
  TCResult :: AST.TypeRepr τ -> AST.Term γ τ -> TCResult γ

-- | Given an untyped list of free variable names and a
--   strongly-typed free variable context, check that the
--   given term is well typed, and, if so, compute what type
--   it has (or report an error).
--
--   The @testEquality@ function is used to reify equality tests
--   on types into the GHC type system.  Pattern matching on @Refl@
--   brings type-level equalities into scope in GHC's type system,
--   and allows the construction of strongly-typed ASTs.  Using
--   the @Except@ monad and monad pattern bindinds, we can have
--   GHC automatically generate error messages if an expected
--   type equality doesn't hold.  This isn't really recommended for
--   production code, as the generated messages are not very user-friendly,
--   but is convenient and fairly readable for demonstration purposes here.

verifyTyping ::
   [String] {-^ Scope information about the free variable names in stack order (nearest enclosing binder nearset to the front of the list -} ->
   Assignment AST.TypeRepr γ {-^ Typed scope information corresponding to the above -} ->
   Term {-^ A term to check -} ->
   Except String (TCResult γ)
verifyTyping scope env tm = case tm of
   TmVar nm ->
     case elemIndex nm scope of
       Just i ->
         case intIndex (length scope - 1 - i) (size env) of
           Just (Some idx) -> return $ TCResult (env!idx) (AST.TmVar idx)
           Nothing -> throwError $ unwords ["Unable to resolve variable:", nm]
       Nothing -> throwError $ unwords ["Variable not in scope:", nm]
   TmInt n ->
     return $ TCResult AST.IntRepr (AST.TmInt n)
   TmBool b ->
     return $ TCResult AST.BoolRepr (AST.TmBool b)
   TmLe x y ->
     do TCResult AST.IntRepr x' <- verifyTyping scope env x
        TCResult AST.IntRepr y' <- verifyTyping scope env y
        return $ TCResult AST.BoolRepr (AST.TmLe x' y')
   TmAdd x y ->
     do TCResult AST.IntRepr x' <- verifyTyping scope env x
        TCResult AST.IntRepr y' <- verifyTyping scope env y
        return $ TCResult AST.IntRepr (AST.TmAdd x' y')
   TmNeg x ->
     do TCResult xtp x' <- verifyTyping scope env x
        Just Refl <- return $ testEquality xtp AST.IntRepr
        return $ TCResult AST.IntRepr (AST.TmNeg x')
   TmIte c x y ->
     do TCResult AST.BoolRepr c' <- verifyTyping scope env c
        TCResult xtp x' <- verifyTyping scope env x
        TCResult ytp y' <- verifyTyping scope env y
        Just Refl <- return $ testEquality xtp ytp
        return $ TCResult xtp (AST.TmIte c' x' y')
   TmApp x y ->
     do TCResult (AST.ArrowRepr argTy outTy) x' <- verifyTyping scope env x
        TCResult ytp y' <- verifyTyping scope env y
        Just Refl <- return $ testEquality ytp argTy
        return $ TCResult outTy (AST.TmApp x' y')
   TmAbs nm tp x ->
     do Some argTy <- return $ typeToRepr tp
        TCResult xtp x' <- verifyTyping (nm:scope) (env :> argTy) x
        return $ TCResult (AST.ArrowRepr argTy xtp) (AST.TmAbs nm argTy x')
   TmFix nm tp x ->
     do Some argTy <- return $ typeToRepr tp
        TCResult xtp x' <- verifyTyping (nm:scope) (env :> argTy) x
        Just Refl <- return $ testEquality argTy xtp
        return $ TCResult xtp (AST.TmFix nm argTy x')

-- | Typecheck a term in the empty typing context.
checkTerm ::
  Term ->
  Except String (TCResult EmptyCtx)
checkTerm = verifyTyping [] Empty
