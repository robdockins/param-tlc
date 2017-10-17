{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}

module Main where

import Control.Monad (forM)
import Control.Monad.ST

import Data.Parameterized.Classes
import Data.Parameterized.Context
import Data.Parameterized.TraversableFC

import TLC.AST
import TLC.Eval

fib :: Term EmptyCtx (IntT :-> IntT)
fib = TmFix knownRepr $ λ $
        TmIte (TmLe (Var @1) 1)
              (Var @1)
              (TmAdd (Var @0 :@ (TmAdd (Var @1) (-1)))
                     (Var @0 :@ (TmAdd (Var @1) (-2))))

fib' :: Term EmptyCtx (IntT :-> IntT)
fib' = λ (TmIte (TmLe (Var @0) 1)
                 (Var @0)
                 (fibaux :@ TmAdd (Var @0) (-2) :@ 1 :@ 1))

 where
 fibaux :: Term (EmptyCtx ::> x) (IntT :-> IntT :-> IntT :-> IntT)
 fibaux  = TmFix knownRepr $ λ $ λ $ λ $
            TmIte (TmLe (Var @2) 0)
                  (Var @4)
                  (Var @1 :@ TmAdd (Var @2) (-1) :@ Var @4 :@ TmAdd (Var @3) (Var @4))

testTerm :: Term EmptyCtx (BoolT :-> IntT :-> BoolT)
testTerm = λ (λ (λ (λ (Var @0)) :@ TmInt 43 :@ TmInt 121))

testTerm1 :: Term EmptyCtx (IntT :-> BoolT)
testTerm1 = testTerm :@ TmBool True

testTerm2 :: Term EmptyCtx BoolT
testTerm2 = testTerm1 :@ TmInt 12

display :: Term EmptyCtx τ -> IO ()
display tm =
  do putStrLn "Original:"
     print tm
     putStrLn "Full β normalization:"
     print (substEval zeroSize tm)
     putStrLn "CBV evaluation:"
     print (cbvEval Empty tm)
     putStrLn "CBN evaluation:"
     putStrLn (runST (show <$> cbnEval Empty tm))
     putStrLn ""


main =
  do display testTerm
     display testTerm1
     display testTerm2

     forM [10 .. 20] $ \n ->
       display (fib :@ TmInt n)

     forM [10 .. 20] $ \n ->
       display (fib' :@ TmInt n)