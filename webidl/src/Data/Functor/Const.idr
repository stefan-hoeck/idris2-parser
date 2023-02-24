module Data.Functor.Const

public export
record Const (a : Type) (b : Type) where
  constructor MkConst
  getConst : a

public export
Eq a => Eq (Const a b) where
  (==) = (==) `on` getConst

public export
Ord a => Ord (Const a b) where
  compare = compare `on` getConst

public export
Show a => Show (Const a b) where
  showPrec p = showCon p "MkConst" . showArg . getConst

public export
Functor (Const a) where
  map _ (MkConst a)= MkConst a

public export
Monoid a => Applicative (Const a) where
  pure _ = MkConst neutral
  MkConst f <*> MkConst a = MkConst $ f <+> a

public export
Foldable (Const a) where
  foldr _ acc _ = acc
  foldl _ acc _ = acc
  null        _ = True

public export
Traversable (Const a) where
  traverse _ (MkConst v) = pure (MkConst v)

public export
Bifunctor Const where
  bimap f _ (MkConst a) = MkConst (f a)

public export
Bifoldable Const where
  bifoldl f _ acc (MkConst a) = f acc a
  bifoldr f _ acc (MkConst a) = f a acc
  binull _ = False

public export
Bitraversable Const where
  bitraverse f _ (MkConst a) = MkConst <$> f a
