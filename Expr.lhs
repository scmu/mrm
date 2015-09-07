{-# LANGUAGE
 DataKinds, KindSignatures, GADTs, TypeOperators, RankNTypes,
 DeriveFunctor, DeriveFoldable, DeriveTraversable, StandaloneDeriving,
 MultiParamTypeClasses, FlexibleInstances, FlexibleContexts,
 UndecidableInstances, OverlappingInstances, NoMonomorphismRestriction,
 LambdaCase
 #-}

module MRM.Expr where

import Control.Monad.Reader hiding (sequence)
import MRM.Infrastructure

data ArithF x  = Num Int | Add x x deriving Functor

type Arith = Fix '[ArithF]

numA :: Int -> Arith
numA x      = inn (Num x)

addA :: Arith -> Arith -> Arith
addA x y    = inn (Add x y)

ppArithAlg :: ArithF String -> String
ppArithAlg (Num x)      = show x
ppArithAlg (Add e1 e2)  = e1 ++ " + " ++ e2

ppArith1 :: Arith -> String
ppArith1 = fold (ppArithAlg ::: Void)

ppArithMatch :: ArithF Arith -> String
ppArithMatch (Num x)      = show x
ppArithMatch (Add e1 e2)  = ppArith2 e1 ++ " + " ++ ppArith2 e2

ppArith2 :: Arith -> String
ppArith2 = match (ppArithMatch ::: Void)


data Val = N Int | B Bool | F

evArith :: ArithF Val -> Val
evArith (Num n)            = N n
evArith (Add (N x) (N y))  = N (x + y)
evArith _                  = F

data LogicF x  = Bol Bool  | If x x x deriving Functor

evLogic :: LogicF Val -> Val
evLogic (Bol n)         = B n
evLogic (If (B b) x y)  = if b then x else y
evLogic _               = F

num :: Mem ArithF fs => Int -> Fix fs
num        = inn . Num

add :: Mem ArithF fs => Fix fs -> Fix fs -> Fix fs
add x y    = inn (Add x y)

bol :: Mem LogicF fs => Bool -> Fix fs
bol        = inn . Bol

iif :: Mem LogicF fs => Fix fs -> Fix fs -> Fix fs -> Fix fs
iif x y z  = inn (If x y z)

type Expr = Fix '[ArithF, LogicF]

eval :: Expr -> Val
eval = fold (evArith ::: evLogic ::: Void)

geval :: Eval fs => Fix fs -> Val
geval = fold evalAlg

class Eval fs where
  evalAlg :: Matches fs Val Val

instance Eval ('[]) where
  evalAlg = Void

instance Eval fs => Eval (ArithF :- fs) where
  evalAlg = evArith ::: evalAlg

instance Eval fs => Eval (LogicF :- fs) where
  evalAlg = evLogic ::: evalAlg

data MulF x = Mul x x deriving Functor

evMul :: MulF Val -> Val
evMul (Mul (N x) (N y))  = N (x * y)
evMul _                  = F

data BindF x = Var String | Let String x x deriving Functor

type Env = [(String,Val)]

evBind :: MonadReader Env m => BindF (m Val) -> m Val
evBind (Var x)        =
  do  env <- ask
      return (maybe F id (lookup x env))
evBind (Let x e1 e2)  =
  do  v1 <- e1
      local ((x,v1):) e2

type Exp3 = Fix '[BindF,ArithF,LogicF]

lett x e1 e2 = inn (Let x e1 e2)

var x = inn (Var x)
