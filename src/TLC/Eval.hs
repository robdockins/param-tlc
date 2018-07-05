{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
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
-- Module               : TLC.Eval
-- Description          : Evaluation strategies for STLC
-- Copyright            : (c) Galois, Inc. 2017
-- Maintainer           : Robert Dockins <rdockins@galois.com>
--
-- This module defines several different evaluation strategies
-- for the STLC.  Each takes advantage of the GADT indices
-- on the term language to ensure that evaluation is well typed.
--
-- Sometimes this requires a very particular way to set up the
-- evaluation definitions.  In particular, the substituion algorithm
-- is most easily expressed using "multi-substitution", which may
-- be less famlilar than single variable substituion.
-------------------------------------------------------------------
module TLC.Eval where

import Control.Monad.Fix
import Control.Monad.ST
import Data.STRef

import Data.Parameterized.Classes
import Data.Parameterized.Context as Ctx hiding ((++))
import Data.Parameterized.TraversableFC

import TLC.AST

-------------------------------------------------------------------
-- Substitution and full-β evaluation
--

-- | A @Subst@ assigns to each free variable in @γ₂@
--   a term with free variables in @γ₁@.
type Subst γ₁ γ₂  = Assignment (Term γ₁) γ₂

-- | This is a utility operation that extends a
--   substitution with a fresh variable that will
--   be unchanged.
extend_sub ::
  Size γ₁ ->
  Subst γ₁ γ₂ ->
  Subst (γ₁ ::> τ) (γ₂ ::> τ)
extend_sub sz sub =
  fmapFC TmWeak sub :> TmVar (nextIndex sz)

-- | Given a substition and a term, apply the substituion to
--   all the free variables in the term.
subst ::
  Size γ₁ ->
  Subst γ₁ γ₂ ->
  Term γ₂ τ -> Term γ₁ τ
subst sz sub tm = case tm of
  TmVar i     -> sub!i
  TmWeak x    -> subst sz (Ctx.init sub) x
  TmBool b    -> TmBool b
  TmInt n     -> TmInt n
  TmLe x y    -> TmLe (subst sz sub x) (subst sz sub y)
  TmAdd x y   -> TmAdd (subst sz sub x) (subst sz sub y)
  TmNeg x     -> TmNeg (subst sz sub x)
  TmIte c x y -> TmIte (subst sz sub c) (subst sz sub x) (subst sz sub y)
  TmApp x y   -> TmApp (subst sz sub x) (subst sz sub y)
  TmAbs nm τ x -> TmAbs nm τ (subst (incSize sz) (extend_sub sz sub) x)
  TmFix nm τ x -> TmFix nm τ (subst (incSize sz) (extend_sub sz sub) x)

-- | Substitute a term for a single open variable, leaving all other
--   variables unchanged.
singleSubst ::
  Size γ ->
  Term γ τ          {- ^ The term to substitute -} ->
  Term (γ ::> τ) τ' {- ^ The term being substituted into -} ->
  Term γ τ'
singleSubst sz tm body = subst sz (generate sz TmVar :> tm) body

-- | Perform full-β normalization on a λ term.
substEval :: Size γ -> Term γ τ -> Term γ τ
substEval sz tm = case tm of
  TmVar i  -> TmVar i
  TmWeak x -> TmWeak (substEval (decSize sz) x)
  TmBool x -> TmBool x
  TmInt n  -> TmInt n
  TmLe x y ->
     case (substEval sz x, substEval sz y) of
       (TmInt a, TmInt b) -> TmBool $! a <= b
       (x',y') -> TmLe x' y'
  TmNeg x ->
     case substEval sz x of
       TmInt a -> TmInt $! negate a
       x' -> TmNeg x'
  TmAdd x y ->
     case (substEval sz x, substEval sz y) of
       (TmInt a, TmInt b) -> TmInt $! a + b
       (x',y') -> TmAdd x' y'
  TmAbs nm τ x  -> TmAbs nm τ (substEval (incSize sz) x)
  TmIte c x y ->
     case substEval sz c of
       TmBool True  -> substEval sz x
       TmBool False -> substEval sz y
       c' -> TmIte c' x y
  TmApp x y ->
     case substEval sz x of
       TmAbs _ _ body -> substEval sz (singleSubst sz y body)
       x' -> TmApp x' y
  TmFix _ _ x ->
     substEval sz (singleSubst sz tm x)

-------------------------------------------------
-- Call by value evaluation

-- | Tie the knot directly through the @Value@ type.
--   This corresponds directly to call-by-value
--   evaluation.
newtype CBV τ = CBV { unCBV :: Value CBV τ }

instance ShowF CBV
instance Show (CBV τ) where
  show (CBV x) = show x

-- | Call-by-value evalaution.  Given an assignment of
--   values to the free variables in @γ@, evaluate the
--   given term to a @Value@.
cbvEval ::
   Assignment CBV γ ->
   Term γ τ ->
   Value CBV τ
cbvEval env tm = case tm of
   TmVar i  -> unCBV (env!i)
   TmWeak x -> cbvEval (Ctx.init env) x
   TmBool b -> VBool b
   TmInt n  -> VInt n
   TmLe x y ->
     case (cbvEval env x, cbvEval env y) of
       -- NB! GHC knows that this is the only possibility!
       (VInt a, VInt b) -> VBool $! a <= b
   TmAdd x y ->
     case (cbvEval env x, cbvEval env y) of
       (VInt a, VInt b) -> VInt $! a + b
   TmNeg x ->
      case cbvEval env x of
        VInt a -> VInt $! negate a
   TmIte c x y ->
     case cbvEval env c of
       VBool True  -> cbvEval env x
       VBool False -> cbvEval env y
   TmAbs _ τ x ->
     -- NB: here we capture the current evaluation environment as a closure
     VAbs env τ x
   TmApp x y ->
     case cbvEval env x of
       VAbs env' _ body ->
         -- NB: we have to @seq@ this to force GHC to evaluate in CBV order
         let y' = CBV (cbvEval env y) in
         seq y' (cbvEval (env' :> y') body)
   TmFix _ _ x ->
     fix $ \x' -> cbvEval (env :> CBV x') x

-------------------------------------------------
-- Call by need evaluation

-- | The @Thunk@ type represents a potentially delayed
--   evaluation operation.  These delayed operations live
--   in the @ST@ monad, so that we can memoize the answers
--   using @STRef@.  If our calculus had side-effects, we might
--   instead embed it in some other monad (e.g. @IO@ or @StateT x (ST s)@).
newtype Thunk s τ = Thunk (STRef s (ST s (CBN s τ)))
type CBN s τ = Value (Thunk s) τ

instance Show (Thunk s τ) where
  show _ = "<thunk>"
instance ShowF (Thunk s)

-- | Given a computation that computes a value,
--   produce a thunk that delays the relevant computation.
delay :: ST s (CBN s τ) -> ST s (Thunk s τ)
delay x = Thunk <$> newSTRef x

-- | Given a delayed evalation thunk, force and
--   memoize its value.
force :: Thunk s τ -> ST s (CBN s τ)
force (Thunk ref) =
   do x <- readSTRef ref
      val <- x
      writeSTRef ref (return val)
      return val

-- | Given an assigment of evaluation thunks to the free variables
--   in @γ@, compute the call-by-need evalaution of the given term.
cbnEval ::
   Assignment (Thunk s) γ ->
   Term γ τ ->
   ST s (CBN s τ)
cbnEval env tm = case tm of
   TmVar i ->
        force (env!i)
   TmWeak x ->
        cbnEval (Ctx.init env) x
   TmBool b ->
        return $ VBool b
   TmInt n ->
        return $ VInt n
   TmLe x y ->
     do VInt a <- cbnEval env x
        VInt b <- cbnEval env y
        return . VBool $! a <= b
   TmAdd x y ->
     do VInt a <- cbnEval env x
        VInt b <- cbnEval env y
        return . VInt $! a + b
   TmNeg x ->
     do VInt a <- cbnEval env x
        return . VInt $! negate a
   TmIte c x y ->
     do VBool c' <- cbnEval env c
        if c' then cbnEval env x else cbnEval env y
   TmAbs _ τ x ->
        return $ VAbs env τ x
   TmApp x y ->
     do VAbs env' _ body <- cbnEval env x
        y' <- delay (cbnEval env y)
        cbnEval (env' :> y') body
   TmFix _ _ x ->
     mfix $ \result ->
       do resultThunk <- delay (return result)
          cbnEval (env :> resultThunk) x
