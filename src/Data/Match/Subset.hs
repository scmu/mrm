{-# LANGUAGE
    GADTs
  , KindSignatures
  , DataKinds
  , TypeOperators
  , MultiParamTypeClasses
  , FlexibleInstances
  , OverlappingInstances
  #-}

module Data.Match.Subset where

import Data.Match.Membership (Elem(..), Mem(witness))

data Sub (fs :: [* -> *]) (gs :: [* -> *]) where
    SNil  :: Sub '[] gs
    SCons :: (Functor f) => Elem f gs -> Sub fs gs -> Sub (f ': fs) gs

class fs <: gs where
    srep :: Sub fs gs

instance '[] <: gs where
    srep = SNil

instance (Functor f, Mem f gs, fs <: gs) => (f ': fs) <: gs where
    srep = SCons witness srep

infix 5 <:


subSub :: Sub fs gs -> Sub fs (g ': gs)
subSub SNil           = SNil
subSub (SCons pos ss) = SCons (There pos) (subSub ss)
