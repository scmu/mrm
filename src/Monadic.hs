{-# LANGUAGE
 DataKinds, KindSignatures, GADTs, TypeOperators, RankNTypes,
 DeriveFunctor, DeriveFoldable, DeriveTraversable,
 MultiParamTypeClasses, FlexibleInstances, FlexibleContexts,
 UndecidableInstances, OverlappingInstances, NoMonomorphismRestriction, LambdaCase, StandaloneDeriving
 #-}

module Monadic where

import Prelude hiding (sequence)
import Data.Traversable
import Control.Monad hiding (sequence)

import Data.Matches

mlift' :: Monad m => TList fs  -> Matches fs a b
                               -> Matches fs (m a) (m b)
mlift'  TNil        Void        = Void
mlift'  (TCons ts)  (k ::: ks)  =
  (liftM k . sequence) ::: mlift' ts ks

mlift ::  (Monad m, Traversables fs) =>
           Matches fs a b -> Matches fs (m a) (m b)
mlift = mlift' trep

transMAlg ::  (Monad m, Traversables fs, fs <: gs) =>
              Algebras fs (m (Fix gs))
transMAlg = mlift transAlg

transM ::  (Monad m, Traversables fs, fs <: gs) =>
           Fix fs -> m (Fix gs)
transM = fold transMAlg
