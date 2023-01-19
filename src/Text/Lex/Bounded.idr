module Text.Lex.Bounded

import Derive.Prelude

%default total

%language ElabReflection

public export
data Bounds : Type where
  MkBounds :
      (startLine : Nat)
   -> (startCol  : Nat)
   -> (endLine   : Nat)
   -> (endCol    : Nat)
   -> Bounds
  NoBounds : Bounds

%runElab derive "Bounds" [Show,Eq]

%inline
pos : Nat -> Nat -> String
pos l c = show (l+1) ++ ":" ++ show (c+1)

export
Interpolation Bounds where
  interpolate (MkBounds sl sc el ec) =
    "\{pos sl sc}--\{pos el ec}"
  interpolate NoBounds = ""

public export
Semigroup Bounds where
  NoBounds <+> y        = y
  x        <+> NoBounds = x
  MkBounds ll1 lc1 ul1 uc1 <+> MkBounds ll2 lc2 ul2 uc2 =
    MkBounds (min ll1 ll2) (min lc1 lc2) (max ul1 ul2) (max uc1 uc2)

public export
Monoid Bounds where
  neutral = NoBounds

public export
record Bounded ty where
  constructor MkBounded
  val    : ty
  bounds : Bounds

%runElab derive "Bounded" [Show,Eq]

public export
bounded : a -> (lstart,cstart,lstop,cstop : Nat) -> Bounded a
bounded v w x y z = MkBounded v $ MkBounds w x y z

public export
app : Bounded (a -> b) -> Bounded a -> Bounded b
app (MkBounded vf b1) (MkBounded va b2) = MkBounded (vf va) (b1 <+> b2)

public export
bind : Bounded a -> (a -> Bounded b) -> Bounded b
bind (MkBounded va b1) f =
  let MkBounded vb b2 = f va
   in MkBounded vb (b1 <+> b2)

public export
Functor Bounded where
  map f (MkBounded val bs) = MkBounded (f val) bs

public export %inline
Applicative Bounded where
  pure v = MkBounded v neutral
  (<*>) = app

public export %inline
Monad Bounded where
  (>>=) = bind

public export
Foldable Bounded where
  foldr c n b = c b.val n
  foldl c n b = c n b.val
  foldMap f b = f b.val
  null _ = False
  toList b = [b.val]

public export
Traversable Bounded where
  traverse f (MkBounded v bs) = (`MkBounded` bs) <$> f v
