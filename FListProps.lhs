{-# LANGUAGE
 DataKinds, KindSignatures, GADTs, TypeOperators, RankNTypes,
 DeriveFunctor, DeriveFoldable, DeriveTraversable, StandaloneDeriving,
 MultiParamTypeClasses, FlexibleInstances, FlexibleContexts,
 UndecidableInstances, OverlappingInstances, NoMonomorphismRestriction,
 FunctionalDependencies, ScopedTypeVariables
 #-}

module MRM.FListProps where

import Data.Foldable hiding (fold, elem)
import Data.Traversable

data FList (fs :: [* -> *]) where
 FNil :: FList '[]
 FCons :: (Functor f) => FList fs -> FList (f ': fs)

class Functors (fs :: [* -> *]) where
 frep :: FList fs

instance Functors '[] where
 frep = FNil

instance (Functor f, Functors fs) => Functors (f ': fs) where
 frep = FCons frep

data FFList (fs :: [* -> *]) where
 FFNil :: FFList '[]
 FFCons :: (Functor f, Foldable f) => FFList fs -> FFList (f ': fs)

class Foldables (fs :: [* -> *]) where
  ffrep :: FFList fs

instance Foldables ('[]) where
  ffrep = FFNil

instance  (Functor f, Foldable f, Foldables fs) =>
          Foldables (f ': fs) where
  ffrep = FFCons ffrep

data TList (fs :: [* -> *]) where
  TNil :: TList '[]
  TCons :: Traversable f => TList fs -> TList (f ': fs)

class Traversables (fs :: [* -> *]) where
  trep :: TList fs

instance Traversables ('[]) where
  trep = TNil

instance  (Traversable f, Traversables fs) =>
          Traversables (f ': fs) where
  trep = TCons trep
