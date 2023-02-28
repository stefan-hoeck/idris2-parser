module Data.Traversable

import Control.Monad.Identity
import Data.Functor.Const
import Data.Morphisms

public export
mapDefault : Traversable t => (a -> b) -> t a -> t b
mapDefault f = runIdentity . traverse (Id . f)

public export
foldrDefault : Traversable t => (a -> acc -> acc) -> acc -> t a -> acc
foldrDefault f acc t =
  (applyEndo . getConst $ traverse (MkConst {b = ()} . Endo . f) t) acc
