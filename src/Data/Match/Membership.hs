{-# LANGUAGE
    CPP
  , GADTs
  , KindSignatures
  , DataKinds
  , TypeOperators
  , MultiParamTypeClasses
  , FlexibleInstances
  #-}

#if __GLASGOW_HASKELL__ < 710
{-# LANGUAGE OverlappingInstances #-}
#endif

module Data.Match.Membership
  ( Elem(..)
  , Mem(witness)
  )
where

data Elem (f :: * -> *) (fs :: [* -> *]) where
    Here  :: Elem f (f ': fs)
    There :: Elem f fs -> Elem f (g ': fs)

class Mem f fs where
    witness :: Elem f fs

instance Mem f (f ': fs) where
    witness = Here

instance
#if __GLASGOW_HASKELL__ >= 710
  {-# OVERLAPPABLE #-}
#endif
  (Mem f fs) => Mem f (g ': fs) where
    witness = There witness
