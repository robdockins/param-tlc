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
import Control.Monad.State.Strict

import qualified Data.IntMap as IntMap
import Data.List
import Data.Maybe
import Data.Type.Equality

--import Data.Parameterized.Classes
import Data.Parameterized.Context hiding ((++))
--import Data.Parameterized.TraversableFC
import Data.Parameterized.Some

import qualified TLC.AST as AST

data TermF (subtm :: *) where
  TmVar  :: String -> TermF subtm
  TmInt  :: Int -> TermF subtm
  TmBool :: Bool -> TermF subtm
  TmLe   :: subtm -> subtm -> TermF subtm 
  TmAdd  :: subtm -> subtm -> TermF subtm
  TmNeg  :: subtm -> TermF subtm
  TmIte  :: subtm -> subtm -> subtm -> TermF subtm
  TmApp  :: subtm -> subtm -> TermF subtm
  TmAbs  :: String -> subtm -> TermF subtm
  TmFix  :: String -> subtm -> TermF subtm

newtype Term = Term { unTerm :: TermF Term }
data TCTerm =
  TCTerm
  { typeOf :: Type
  , valueOf :: TermF TCTerm
  }

data Type where
  VarT :: Int -> Type
  IntT :: Type
  BoolT :: Type
  ArrowT :: Type -> Type -> Type
 deriving (Show)

data TCState =
  TCState
  { tc_tvars   :: IntMap.IntMap (Maybe Type)
  , tc_nextvar :: Int
  , tc_scope   :: [(String,Type)]
  }

newtype TC a = TC { unTC :: StateT TCState (Except String) a }
 deriving (Functor, Applicative, Monad)

deriving instance MonadError String TC


data TCResult γ where
  TCResult :: AST.TypeRepr τ -> AST.Term γ τ -> TCResult γ

runTC :: [String] {- ^ Initial scope -} ->
         TC a ->
         Except String (a, TCState)
runTC scope (TC x) = runStateT x initSt
 where
 initSt = TCState
          { tc_tvars   = mempty
          , tc_nextvar = length scope
          , tc_scope   = reverse $ zip scope $ map VarT [0..]
          }

withExtendedScope ::
   String ->
   Maybe Type ->
   TC a ->
   TC (Type, a)
withExtendedScope nm (Just tp) (TC action) = TC $
   do st <- get
      let oldscope = tc_scope st
      put st{ tc_scope = (nm,tp) : oldscope }
      a <- action
      modify (\x -> x{ tc_scope = oldscope })
      return (tp, a)
withExtendedScope nm Nothing (TC action) = TC $
   do st <- get
      let v    = tc_nextvar st
      let oldscope = tc_scope st
      let sc   = (nm,VarT v) : oldscope
      let vars = IntMap.insert v Nothing (tc_tvars st)
      put TCState{ tc_tvars = vars
                 , tc_nextvar = v+1
                 , tc_scope   = sc
                 }
      a <- action
      modify (\x -> x{ tc_scope = oldscope })
      return (VarT v, a)

freshType :: TC Type
freshType = TC $
  do st <- get
     let v = tc_nextvar st
     let vars = IntMap.insert v Nothing (tc_tvars st)
     put st{ tc_tvars = vars
           , tc_nextvar = v+1
           }
     return (VarT v)


unifyVar :: Int -> Type -> TC ()
unifyVar i x = TC $
  do st <- get
     case IntMap.lookup i (tc_tvars st) of
       Nothing -> throwError $ unwords ["Unknown type variable", show i]
       Just Nothing  -> put st{ tc_tvars = IntMap.insert i (Just x) (tc_tvars st) }
       Just (Just y) -> unTC (unify x y)

unify :: Type -> Type -> TC ()
unify (VarT i) y  = unifyVar i y
unify x (VarT i)  = unifyVar i x
unify IntT  IntT  = return ()
unify BoolT BoolT = return ()
unify (ArrowT x₁ x₂) (ArrowT y₁ y₂) =
   do unify x₁ y₁
      unify x₂ y₂
unify x y =
  throwError $ unwords ["Could not unify types", show x, show y]


typecheckVar ::
  String ->
  TC Type
typecheckVar nm = TC $
  do st <- get
     case lookup nm (tc_scope st) of
       Just tp -> return tp
       Nothing -> throwError $ unwords ["unknown variable:", nm]

typecheck ::
  Term ->
  TC TCTerm
typecheck (Term tm) = case tm of
  TmVar nm ->
    do tp <- typecheckVar nm
       return $ TCTerm tp (TmVar nm)
  TmInt x ->
       return $ TCTerm IntT (TmInt x)
  TmBool b ->
       return $ TCTerm BoolT (TmBool b)
  TmLe x y ->
    do x' <- typecheck x
       y' <- typecheck y
       unify IntT (typeOf x')
       unify IntT (typeOf y')
       return $ TCTerm BoolT (TmLe x' y')
  TmAdd x y ->
    do x' <- typecheck x
       y' <- typecheck y
       unify IntT (typeOf x')
       unify IntT (typeOf y')
       return $ TCTerm IntT (TmAdd x' y')
  TmNeg x ->
    do x' <- typecheck x
       unify IntT (typeOf x')
       return $ TCTerm IntT (TmNeg x')
  TmIte c x y ->
    do c' <- typecheck c
       x' <- typecheck x
       y' <- typecheck y
       unify BoolT (typeOf c')
       unify (typeOf x') (typeOf y')
       return $ TCTerm (typeOf x') (TmIte c' x' y')
  TmApp x y ->
    do x' <- typecheck x
       y' <- typecheck y
       tout <- freshType
       unify (typeOf x') (ArrowT (typeOf y') tout)
       return $ TCTerm tout (TmApp x' y')
  TmAbs nm x ->
    do (targ, x') <- withExtendedScope nm Nothing (typecheck x)
       return $ TCTerm (ArrowT targ (typeOf x')) (TmAbs nm x')
  TmFix nm x ->
    do (targ, x') <- withExtendedScope nm Nothing (typecheck x)
       unify targ (typeOf x')
       return $ TCTerm (typeOf x') (TmFix nm x')

resolveDefaulting ::
   IntMap.IntMap (Maybe Type) ->
   IntMap.IntMap Type
resolveDefaulting = fmap (fromMaybe IntT)

resolveType ::
   IntMap.IntMap Type ->
   Type ->
   Except String (Some AST.TypeRepr)
resolveType tvars t = case t of
  VarT i ->
    case IntMap.lookup i tvars of
      Just t -> resolveType tvars t
      Nothing -> throwError $ unwords ["unable to resolve type variable", show i]
  IntT  -> return $ Some AST.IntRepr
  BoolT -> return $ Some AST.BoolRepr
  ArrowT x y ->
    do Some x' <- resolveType tvars x
       Some y' <- resolveType tvars y
       return $ Some (AST.ArrowRepr x' y')

verifyTyping ::
   IntMap.IntMap Type ->
   [String] ->
   Assignment AST.TypeRepr γ ->   
   TCTerm ->
   Except String (TCResult γ)
verifyTyping tvars scope env (TCTerm tp tm) = case tm of
   TmVar nm ->
     case elemIndex nm scope of
       Just i ->
         case intIndex (length scope - i) (size env) of
           Just (Some idx) -> return $ TCResult (env!idx) (AST.TmVar idx)
           Nothing -> throwError $ unwords ["unable to resolve variable:", nm]
       Nothing -> throwError $ unwords ["Variable not in scope:", nm]
   TmInt n ->
     return $ TCResult AST.IntRepr (AST.TmInt n)
   TmBool b ->
     return $ TCResult AST.BoolRepr (AST.TmBool b)
   TmLe x y ->
     do TCResult xtp x' <- verifyTyping tvars scope env x
        TCResult ytp y' <- verifyTyping tvars scope env y
        Just Refl <- return $ testEquality xtp AST.IntRepr
        Just Refl <- return $ testEquality ytp AST.IntRepr
        return $ TCResult AST.BoolRepr (AST.TmLe x' y')
   TmAdd x y ->
     do TCResult xtp x' <- verifyTyping tvars scope env x
        TCResult ytp y' <- verifyTyping tvars scope env y
        Just Refl <- return $ testEquality xtp AST.IntRepr
        Just Refl <- return $ testEquality ytp AST.IntRepr
        return $ TCResult AST.IntRepr (AST.TmAdd x' y')
   TmNeg x ->
     do TCResult xtp x' <- verifyTyping tvars scope env x
        Just Refl <- return $ testEquality xtp AST.IntRepr
        return $ TCResult AST.IntRepr (AST.TmNeg x')
   TmIte c x y ->
     do TCResult ctp c' <- verifyTyping tvars scope env c
        TCResult xtp x' <- verifyTyping tvars scope env x
        TCResult ytp y' <- verifyTyping tvars scope env y
        Just Refl <- return $ testEquality ctp AST.BoolRepr
        Just Refl <- return $ testEquality xtp ytp
        return $ TCResult xtp (AST.TmIte c' x' y')
   TmApp x y ->
     do TCResult xtp x' <- verifyTyping tvars scope env x
        TCResult ytp y' <- verifyTyping tvars scope env y
        case xtp of
          AST.ArrowRepr argTy outTy ->
            do Just Refl <- return $ testEquality ytp argTy
               return $ TCResult outTy (AST.TmApp x' y')
          _ -> throwError "Expected function type in application"
   TmAbs nm x ->
     do Some argTy <- resolveType tvars tp
        TCResult xtp x' <- verifyTyping tvars (nm:scope) (env :> argTy) x
        return $ TCResult (AST.ArrowRepr argTy xtp) (AST.TmAbs argTy x')
   TmFix nm x ->
     do Some argTy <- resolveType tvars tp
        TCResult xtp x' <- verifyTyping tvars (nm:scope) (env :> argTy) x
        Just Refl <- return $ testEquality argTy xtp
        return $ TCResult xtp (AST.TmFix argTy x')


checkTerm ::
  Term -> Except String (TCResult EmptyCtx)
checkTerm t =
  do (t',st) <- runTC [] (typecheck t)
     let tvars = resolveDefaulting (tc_tvars st)
     verifyTyping tvars [] Empty t'
