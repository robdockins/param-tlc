{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
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

module TLC.Eval where

import Control.Monad.Fix
import Control.Monad.ST
import Data.STRef

import Data.Parameterized.Classes
import Data.Parameterized.Context hiding ((++))
import Data.Parameterized.TraversableFC

import TLC.AST

-------------------------------------------------------------------
-- Weakening, substitution, and full-β evaluation
--

type Weaken γ₁ γ₂ = Assignment (Index γ₁) γ₂
type Subst γ₁ γ₂  = Assignment (Term γ₁) γ₂

extend_wk ::
  Size γ₁ ->
  Weaken γ₁ γ₂ ->
  Weaken (γ₁ ::> τ) (γ₂ ::> τ)
extend_wk sz wk =
  fmapFC skip wk :> nextIndex sz

weaken ::
  Size γ₁ ->
  Weaken γ₁ γ₂ ->
  Term γ₂ τ -> Term γ₁ τ
weaken sz wk tm = case tm of
  TmVar i     -> TmVar (wk!i)
  TmBool b    -> TmBool b
  TmInt n     -> TmInt n
  TmLe x y    -> TmLe (weaken sz wk x) (weaken sz wk y)
  TmAdd x y   -> TmAdd (weaken sz wk x) (weaken sz wk y)
  TmNeg x     -> TmNeg (weaken sz wk x)
  TmIte c x y -> TmIte (weaken sz wk c) (weaken sz wk x) (weaken sz wk y)
  TmApp x y   -> TmApp (weaken sz wk x) (weaken sz wk y)
  TmAbs x     -> TmAbs (weaken (incSize sz) (extend_wk sz wk) x)
  TmFix x     -> TmFix (weaken (incSize sz) (extend_wk sz wk) x)

extend_sub ::
  Size γ₁ ->
  Subst γ₁ γ₂ ->
  Subst (γ₁ ::> τ) (γ₂ ::> τ)
extend_sub sz sub =
  fmapFC (weaken (incSize sz) (generate sz (\i -> skip i))) sub :> (TmVar (nextIndex sz))

subst ::
  Size γ₁ ->
  Subst γ₁ γ₂ ->
  Term γ₂ τ -> Term γ₁ τ
subst sz sub tm = case tm of
  TmVar i     -> sub!i
  TmBool b    -> TmBool b
  TmInt n     -> TmInt n
  TmLe x y    -> TmLe (subst sz sub x) (subst sz sub y)
  TmAdd x y   -> TmAdd (subst sz sub x) (subst sz sub y)
  TmNeg x     -> TmNeg (subst sz sub x)
  TmIte c x y -> TmIte (subst sz sub c) (subst sz sub x) (subst sz sub y)
  TmApp x y   -> TmApp (subst sz sub x) (subst sz sub y)
  TmAbs x     -> TmAbs (subst (incSize sz) (extend_sub sz sub) x)
  TmFix x     -> TmFix (subst (incSize sz) (extend_sub sz sub) x)

substEval :: Size γ -> Term γ τ -> Term γ τ
substEval sz tm = case tm of
  TmVar i  -> TmVar i
  TmBool x -> TmBool x
  TmInt n  -> TmInt n
  TmLe x y ->
     case (substEval sz x, substEval sz y) of
       (TmInt a, TmInt b) -> TmBool $! a <= b
       (x',y') -> TmLe x' y'
  TmNeg x ->
     case substEval sz x of
       TmInt a -> TmInt $! negate a
       x' -> TmNeg x
  TmAdd x y ->
     case (substEval sz x, substEval sz y) of
       (TmInt a, TmInt b) -> TmInt $! a + b
       (x',y') -> TmAdd x' y'
  TmAbs x  -> TmAbs (substEval (incSize sz) x)
  TmIte c x y ->
     case substEval sz c of
       TmBool True  -> substEval sz x
       TmBool False -> substEval sz y
       c' -> TmIte c' x y
  TmApp x y ->
     case substEval sz x of
       TmAbs body -> substEval sz (subst sz (generate sz TmVar :> y) body)
       x' -> TmApp x' y
  TmFix x ->
     substEval sz (subst sz (generate sz TmVar :> tm) x)

-------------------------------------------------
-- Call by value evaluation

newtype CBV τ = CBV { unCBV :: Value CBV τ }

instance ShowF CBV where
  showF (CBV x) = show x
instance Show (CBV τ) where
  show = showF

cbvEval ::
   Assignment CBV γ ->
   Term γ τ ->
   Value CBV τ
cbvEval env tm = case tm of
   TmVar i  -> unCBV (env!i)
   TmBool b -> VBool b
   TmInt n  -> VInt n
   TmLe x y ->
     case (cbvEval env x, cbvEval env y) of
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
   TmAbs x -> VAbs env x
   TmApp x y ->
     case cbvEval env x of
       VAbs env' body ->
         let y' = CBV $ cbvEval env y in
         seq y' (cbvEval (env' :> y') body)
   TmFix x ->
     fix $ \x' -> cbvEval (env :> CBV x') x

-------------------------------------------------
-- Call by need evaluation

type CBN s τ = Value (Thunk s) τ
newtype Thunk s τ = Thunk (STRef s (ST s (CBN s τ)))

instance Show (Thunk s τ) where
  show = showF
instance ShowF (Thunk s) where
  showF _ = "<thunk>"

delay :: ST s (CBN s τ) -> ST s (Thunk s τ)
delay x = Thunk <$> newSTRef x

force :: Thunk s τ -> ST s (CBN s τ)
force (Thunk ref) =
   do x <- readSTRef ref
      val <- x
      writeSTRef ref (return val)
      return val

cbnEval ::
   Assignment (Thunk s) γ ->
   Term γ τ ->
   ST s (CBN s τ)
cbnEval env tm = case tm of
   TmVar i  -> force (env!i)
   TmBool b -> return $ VBool b
   TmInt n  -> return $ VInt n
   TmLe x y ->
     do x' <- cbnEval env x
        y' <- cbnEval env y
        case (x',y') of
          (VInt a, VInt b) -> return . VBool $! a <= b
   TmAdd x y ->
     do x' <- cbnEval env x
        y' <- cbnEval env y
        case (x',y') of
          (VInt a, VInt b) -> return . VInt $! a + b
   TmNeg x ->
     do x' <- cbnEval env x
        case x' of
          VInt a -> return . VInt $! negate a
   TmIte c x y ->
     do cbnEval env c >>= \case
          VBool True  -> cbnEval env x
          VBool False -> cbnEval env y
   TmAbs x -> return $ VAbs env x
   TmApp x y ->
     do cbnEval env x >>= \case
          VAbs env' body ->
            do y' <- delay (cbnEval env y)
               cbnEval (env' :> y') body
   TmFix x ->
     mfix $ \x' ->
       do xthunk <- delay (return x')
          cbnEval (env :> xthunk) x
