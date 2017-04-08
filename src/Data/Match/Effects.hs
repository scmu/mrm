{-# LANGUAGE
    DataKinds
  , TypeOperators
  , UndecidableInstances
  , FlexibleContexts
  , DeriveFunctor
  , LambdaCase
  #-}

module Data.Match.Effects where

import Data.Match
import Data.Match.Fix
import Data.Match.Membership
import Data.Match.Subset

import Control.Applicative (Applicative(pure, (<*>)))
import Control.Monad (liftM2, ap)

data Pure a x = Pure a deriving (Show, Functor)

newtype Free fs a = Free { getFix :: Fix (Pure a ': fs) }

free :: (Functor f, Mem f fs) => f (Free fs a) -> Free fs a
free m = Free . In (There witness) . fmap getFix $ m

transFree :: (fs <: gs) => Algebras fs (Free gs a)
transFree = Free ^<< transAlgWith (subSub srep) <<^ getFix

transFreeSym :: (fs <: gs) => Algebras (Pure a ': fs) (Free gs a)
transFreeSym = Free ^<< transAlgWith (SCons Here (subSub srep)) <<^ getFix

instance (fs <: fs) => Functor (Free fs) where
    fmap f = fold ((\(Pure x) -> Free (inn (Pure (f x)))) ::: transFree) . getFix

instance (fs <: fs) => Monad (Free fs) where
    return         = Free . inn . Pure
    (Free p) >>= f = fold ((\(Pure x) -> f x) :::
                           transFree) p

instance (Monad (Free fs), Functor (Free fs)) => Applicative (Free fs) where
    pure = return
    (<*>) = ap

subProg :: (fs <: gs) => Free fs a -> Free gs a
subProg = fold ((\(Pure x) -> Free . inn . Pure $ x) :::
                transFree) . getFix

runPure :: Free '[] a -> a
runPure = match ((\ (Pure x) -> x) ::: Void) . getFix

data State s  x = Get (s -> x) | Put s x deriving (Functor)
data Nondet   x = Or x x deriving (Show, Functor)
data Except e x = Throw e deriving (Show, Functor)

choose :: (fs <: fs, Mem Nondet fs) => a -> a -> Free fs a
choose a1 a2 = free (Or (return a1) (return a2))

throw :: (fs <: fs, Mem (Except e) fs) => e -> Free fs a
throw e = free (Throw e)

get :: (fs <: fs, Mem (State s) fs) => Free fs s
get = free (Get return)

put :: (fs <: fs, Mem (State s) fs) => s -> Free fs ()
put s = free (Put s (return ()))

runNondet :: (fs <: fs) => Free (Nondet ': fs) a -> Free fs [a]
runNondet = fold ((\(Pure x)   -> return [x]) :::
                  (\(Or mx my) -> liftM2 (++) mx my) :::
                  transFree) . getFix

runExcept :: (fs <: fs) => Free (Except e ': fs) a -> Free fs (Either e a)
runExcept = fold ((\case Pure x  -> return (Right x)) :::
                  (\case Throw e -> return (Left e)) :::
                  transFree) . getFix

catch :: (fs <: fs, Mem (Except e) fs) => Free fs a -> (e -> Free fs a) -> Free fs a
catch m hdlr = fold ((\case Pure x  -> return x) :::
                     (\case Throw e -> hdlr e) >::
                     transFree) . getFix $ m

runState   :: (fs <: fs) => Free (State s ': fs) a ->
                            (s -> Free fs (a, s))
runState =
    fold ((\case Pure x   -> (\s -> return (x, s))) :::
          (\case Get g    -> (\s -> g s s)
                 Put s' k -> (\s -> k s')) :::
          algST) . getFix

algST :: (fs <: fs) => Algebras fs (s -> Free fs (a, s))
algST = (Free .) ^<<
        fromFunctionWith (\ pos m s -> In pos (fmap ($ s) m))
                         (subSub srep)
        <<^ (getFix .)
