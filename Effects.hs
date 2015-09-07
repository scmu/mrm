{-# LANGUAGE
 RankNTypes, ScopedTypeVariables, DataKinds, KindSignatures, GADTs,
 TypeOperators, MultiParamTypeClasses, FlexibleInstances, UndecidableInstances,
 FlexibleContexts, DeriveFunctor, LambdaCase, StandaloneDeriving
 #-}

module MRM.Effects where

import Control.Applicative
import Control.Monad (liftM2, ap)

import MRM.Infrastructure

data Pure a x = Pure a

newtype Free fs a = Free { getFix :: Fix (Pure a :- fs) }

free :: (Functor f, Mem f fs) => f (Free fs a) -> Free fs a
free m = Free . In (There witness) . fmap getFix $ m

transFree :: (fs <: gs) => Algebras fs (Free gs a)
transFree = Free ^<< transAlg' (subSub srep) <<^ getFix

transFreeSym :: (fs <: gs) => Algebras (Pure a :- fs) (Free gs a)
transFreeSym = Free ^<< transAlg' (SCons Here (subSub srep)) <<^ getFix

instance (fs <: fs) => Monad (Free fs) where
  return         = Free . inn . Pure
  (Free p) >>= f = fold (  (\ (Pure x) -> f x) :::
                           transFree ) p

instance (Monad (Free fs), Functor (Free fs)) => Applicative (Free fs) where
  pure = return
  (<*>) = ap

subProg :: (fs <: gs) => Free fs a -> Free gs a
subProg = fold (  (\ (Pure x) -> Free . inn . Pure $ x) :::
                  transFree) . getFix

runPure :: Free '[] a -> a
runPure = match ((\ (Pure x) -> x) ::: Void) . getFix

data State s   x  = Get (s -> x) | Put s x
data Nondet    x  = Or x x
data Except e  x  = Throw e

choose  :: (fs <: fs, Mem Nondet fs)      => a -> a ->  Free fs a
throw   :: (fs <: fs, Mem (Except e) fs)  => e ->       Free fs a
get     :: (fs <: fs, Mem (State s) fs)   =>            Free fs s
put     :: (fs <: fs, Mem (State s) fs)   => s ->       Free fs ()

choose a1 a2 = free (Or (return a1) (return a2))
get = free (Get return)
put s = free (Put s (return ()))
throw e = free (Throw e)

runNondet  :: (fs <: fs) =>  Free (Nondet :- fs) a -> Free fs [a]
runNondet = fold (  (\ (Pure x)    -> return [x]) :::
                    (\ (Or mx my)  -> liftM2 (++) mx my) :::
                    transFree) . getFix

runExcept  :: (fs <: fs) =>  Free (Except e :- fs) a ->
                             Free fs (Either e a)
runExcept = fold (  (\case Pure x   -> return (Right x)) :::
                    (\case Throw e  -> return (Left e)) :::
                    transFree) . getFix

catch :: (fs <: fs, Mem (Except e) fs) =>
  Free fs a -> (e -> Free fs a) -> Free fs a
catch m hdlr = fold (  (\case Pure x   -> return x) :::
                       (\case Throw e  -> hdlr e) >::
                       transFree) . getFix $ m

runState   :: (fs <: fs) =>  Free (State s :- fs) a ->
                             (s -> Free fs (a, s))
runState =
  fold (  (\case  Pure x    -> (\s -> return (x, s))) :::
          (\case  Get g     -> (\s -> g s s)
                  Put s' k  -> (\s -> k s')) :::
          algST) . getFix
algST :: (fs <: fs) => Algebras fs (s -> Free fs (a, s))
algST =  (Free .)  ^<<
         generateMatches' (\ pos m s -> In pos (fmap ($ s) m))
                          (subSub srep)
         <<^ (getFix .)

dec ::  (  Mem (State Int) fs, Mem Nondet fs,
           Mem (Except String) fs, fs <: fs) => Free fs ()
dec = do  n :: Int <- get
          if n < 0 then throw "negative"
          else do {i <- choose 1 2; put (n + i)}

deriving instance Functor (Pure a)
deriving instance Functor Nondet
deriving instance Functor (State s)
deriving instance Functor (Except e)

deriving instance Show a => Show (Pure a x)
deriving instance Show x => Show (Nondet x)
deriving instance Show e => Show (Except e x)
