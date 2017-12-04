{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}

module Main where

import Control.Monad (forM)
import Control.Monad.ST
import Control.Monad.Except
import System.IO


import Data.Parameterized.Classes
import Data.Parameterized.Context
import Data.Parameterized.TraversableFC

import TLC.AST
import TLC.Eval
import qualified TLC.TypeCheck as T

testTerm :: T.Term
testTerm =
       T.TmAbs "a" T.BoolT $
       T.TmAbs "b" T.IntT $
         (T.TmAbs "x" T.IntT $
          T.TmAbs "y" T.IntT $
            (T.TmVar "a"))
         `T.TmApp`
           T.TmInt 43
         `T.TmApp`
           T.TmInt 121


fib :: Term EmptyCtx (IntT :-> IntT)
fib = μ "fib" $ λ "x" $
        TmIte (Var @1 :<= 1)
              (Var @1)
              ((Var @0 :@ (Var @1 + (-1)))
                + 
               (Var @0 :@ (Var @1 + (-2)))
              )

fib' :: Term EmptyCtx (IntT :-> IntT)
fib' = λ "x" (TmIte (Var @0 :<= 1)
                (Var @0)
                (TmWeak fibaux :@ Var @0 + (-2) :@ 1 :@ 1))

 where
 fibaux :: Term EmptyCtx (IntT :-> IntT :-> IntT :-> IntT)
 fibaux  = μ "fibaux" $ λ "n" $ λ "x" $ λ "y" $
            TmIte (Var @1 :<= 0)
                  (Var @3)
                  (Var @0 :@ Var @1 + (-1) :@ Var @3 :@ (Var @2) + (Var @3))

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


readMain :: [String] -> IO ()
readMain tms =
  do results <- checkTerms tms

     forM_ results (\case
        T.TCResult tp tm ->
          do putStrLn "Type:"
             print tp
             display tm)

     T.TCResult tp t <- applyTerms results
     display t


applyTerms :: [T.TCResult γ] -> IO (T.TCResult γ)
applyTerms [] = fail "Empty list of terms!"
applyTerms (T.TCResult tp f : xs) = go tp f xs
 where
 go :: TypeRepr τ -> Term γ τ -> [T.TCResult γ] -> IO (T.TCResult γ)
 go tp tm [] = return $ T.TCResult tp tm
 go (ArrowRepr τ₁ τ₂) f (T.TCResult σ x : ts)
   | Just Refl <- testEquality τ₁ σ
   = go τ₂ (f :@ x) ts
 go tp _ (T.TCResult xtp _ : _)
   = fail $ unwords [ "Cannot apply term of type", show tp, "to a term of type", show xtp]  


checkTerms :: [String] -> IO [T.TCResult EmptyCtx]
checkTerms [] = return []
checkTerms (t:ts) =
  do Right t' <- return . runExcept . T.checkTerm . read $ t
     ts' <- checkTerms ts
     return (t':ts')

testMain :: IO ()
testMain =
  do Right (T.TCResult tp t) <- return $ runExcept (T.checkTerm testTerm)
     Just Refl <- return $ testEquality tp (ArrowRepr BoolRepr (ArrowRepr IntRepr BoolRepr))

     display t
     display (t :@ TmBool True)
     display (t :@ TmBool True :@ TmInt 12)

     -- display testTerm
     -- display testTerm1
     -- display testTerm2

fibMain :: IO ()
fibMain =
  do forM_ [10 .. 20] $ \n ->
        display (fib' :@ TmInt n)


main :: IO ()
--main = testMain
--main = fibMain
main = getContents >>= readMain . lines

