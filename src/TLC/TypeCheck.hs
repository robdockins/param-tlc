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

module TLC.TypeCheck where

import Control.Monad.Except

import Data.List
import Data.Type.Equality

import Data.Parameterized.Context hiding ((++))
import Data.Parameterized.Some

import qualified TLC.AST as AST

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

data TCResult γ where
  TCResult :: AST.TypeRepr τ -> AST.Term γ τ -> TCResult γ

verifyTyping ::
   [String] ->
   Assignment AST.TypeRepr γ ->
   Term ->
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
     do TCResult xtp x' <- verifyTyping scope env x
        TCResult ytp y' <- verifyTyping scope env y
        Just Refl <- return $ testEquality xtp AST.IntRepr
        Just Refl <- return $ testEquality ytp AST.IntRepr
        return $ TCResult AST.BoolRepr (AST.TmLe x' y')
   TmAdd x y ->
     do TCResult xtp x' <- verifyTyping scope env x
        TCResult ytp y' <- verifyTyping scope env y
        Just Refl <- return $ testEquality xtp AST.IntRepr
        Just Refl <- return $ testEquality ytp AST.IntRepr
        return $ TCResult AST.IntRepr (AST.TmAdd x' y')
   TmNeg x ->
     do TCResult xtp x' <- verifyTyping scope env x
        Just Refl <- return $ testEquality xtp AST.IntRepr
        return $ TCResult AST.IntRepr (AST.TmNeg x')
   TmIte c x y ->
     do TCResult ctp c' <- verifyTyping scope env c
        TCResult xtp x' <- verifyTyping scope env x
        TCResult ytp y' <- verifyTyping scope env y
        Just Refl <- return $ testEquality ctp AST.BoolRepr
        Just Refl <- return $ testEquality xtp ytp
        return $ TCResult xtp (AST.TmIte c' x' y')
   TmApp x y ->
     do TCResult xtp x' <- verifyTyping scope env x
        TCResult ytp y' <- verifyTyping scope env y
        case xtp of
          AST.ArrowRepr argTy outTy ->
            do Just Refl <- return $ testEquality ytp argTy
               return $ TCResult outTy (AST.TmApp x' y')
          _ -> throwError "Expected function type in application"
   TmAbs nm tp x ->
     do Some argTy <- return $ typeToRepr tp
        TCResult xtp x' <- verifyTyping (nm:scope) (env :> argTy) x
        return $ TCResult (AST.ArrowRepr argTy xtp) (AST.TmAbs argTy x')
   TmFix nm tp x ->
     do Some argTy <- return $ typeToRepr tp
        TCResult xtp x' <- verifyTyping (nm:scope) (env :> argTy) x
        Just Refl <- return $ testEquality argTy xtp
        return $ TCResult xtp (AST.TmFix argTy x')

checkTerm ::
  Term ->
  Except String (TCResult EmptyCtx)
checkTerm = verifyTyping [] Empty
