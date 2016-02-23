{-# LANGUAGE
    GADTs
  , KindSignatures
  , DataKinds
  , TypeOperators
  , RankNTypes
  #-}

module Data.Match
  ( module Data.Match
  , module Data.Match.Fix
  , module Data.Match.Membership
  , module Data.Match.Subset
  )
where

import Data.Match.Fix
import Data.Match.Membership
import Data.Match.Subset

data Match (fs :: [* -> *]) (a :: *) (b :: *) where
    Void  :: Match '[] a b
    (:::) :: Functor f => (f a -> b) -> Match fs a b -> Match (f ': fs) a b

infixr 6 :::

extractAt :: Elem f fs -> Match fs a b -> (f a -> b)
extractAt Here        (f :::  _) = f
extractAt (There pos) (_ ::: fs) = extractAt pos fs

overrideAt :: Elem f fs -> (f a -> b) -> Match fs a b -> Match fs a b
overrideAt Here        g (_ ::: fs) = g ::: fs
overrideAt (There pos) g (f ::: fs) = f ::: overrideAt pos g fs

(>::) :: Mem f fs =>  (f a -> b) -> Match fs a b -> Match fs a b
(>::) = overrideAt witness

infixr 6 >::

fromFunctionWith :: (forall f. Functor f => Elem f fs -> f a -> b) -> Sub gs fs -> Match gs a b
fromFunctionWith f SNil = Void
fromFunctionWith f (SCons pos ss) = f pos ::: fromFunctionWith f ss

fromFunction :: (fs <: fs) => (forall f. Functor f => Elem f fs -> f a -> b) -> Match fs a b
fromFunction f = fromFunctionWith f srep

(<<^) :: Match fs b c -> (a -> b) -> Match fs a c
Void <<^ g       = Void
(h ::: hs) <<^ g = h . fmap g ::: hs <<^ g

(^<<) :: (b -> c) -> Match fs a b -> Match fs a c
g ^<< Void       = Void
g ^<< (h ::: hs) = g . h ::: g ^<< hs

(&&&) :: Match fs a b -> Match fs a c -> Match fs a (b,c)
Void &&& Void = Void
(h ::: hs) &&& (k ::: ks) = (\x -> (h x, k x)) ::: (hs &&& ks)

infixr 7 <<^, ^<<
infixr 5 &&&

match :: Match fs (Fix fs) b -> Fix fs -> b
match fs (In pos xs) = extractAt pos fs xs

prj :: (Mem f fs, fs <: fs) => Fix fs -> Maybe (f (Fix fs))
prj = match (Just >:: fromFunction (\pos -> const Nothing))

type Algebras fs a = Match fs a a

inns :: (fs <: fs) => Algebras fs (Fix fs)
inns = transAlg

transAlgWith :: Sub fs gs -> Algebras fs (Fix gs)
transAlgWith SNil           = Void
transAlgWith (SCons pos xs) = In pos ::: transAlgWith xs

transAlg :: (fs <: gs) => Algebras fs (Fix gs)
transAlg = transAlgWith srep

fold :: Algebras fs a -> Fix fs -> a
fold ks (In pos xs) = extractAt pos ks (fmap (fold ks) xs)

para :: (fs <: fs) => Match fs (a, Fix fs) a -> Fix fs -> a
para ks = fst . fold (ks &&& (inns <<^ snd))

mfold :: (forall r. (r -> a) -> Match gs r a) -> Fix gs -> a
mfold f (In pos xs) = extractAt pos (f (mfold f)) xs

subOp :: (fs <: gs) => (Fix gs -> c) -> Fix fs -> c
subOp f = f . subFix

subFix :: (fs <: gs) => Fix fs -> Fix gs
subFix = fold transAlg

subMatchWith :: Sub fs gs -> Match gs r a -> Match fs r a
subMatchWith SNil           _  = Void
subMatchWith (SCons pos xs) as = extractAt pos as ::: subMatchWith xs as

subMatch :: (fs <: gs) => Match gs r a -> Match fs r a
subMatch = subMatchWith srep

instance Functor (Match fs a) where
    fmap = (^<<)
