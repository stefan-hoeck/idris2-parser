module Data.Bitraversable

import Control.Monad.Identity
import Data.Functor.Const
import Data.Morphisms

public export
bimapDefault : Bitraversable p => (a -> c) -> (b -> d) -> p a b -> p c d
bimapDefault f g = runIdentity . bitraverse (Id . f) (Id . g)

public export
bifoldrDefault : Bitraversable p =>
                 (a -> acc -> acc) -> (b -> acc -> acc) -> acc -> p a b -> acc
bifoldrDefault f g acc t =
  (applyEndo . getConst $ bitraverse (endo f) (endo g) t) acc
  where endo : forall x,y . (x -> y -> y) -> x -> Const (Endomorphism y) ()
        endo f = MkConst . Endo . f
