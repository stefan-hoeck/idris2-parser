module Text.Lex.Bounded

import Derive.Prelude

%default total

%language ElabReflection

public export
data Bounds : Type where
  BS :
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

namespace Bounds
  public export
  oneChar : (l,c : Nat) -> Bounds
  oneChar l c = BS l c l (S c)

export
Interpolation Bounds where
  interpolate (BS sl sc el ec) =
    "\{pos sl sc}--\{pos el ec}"
  interpolate NoBounds = ""

public export
Semigroup Bounds where
  NoBounds <+> y        = y
  x        <+> NoBounds = x
  BS ll1 lc1 ul1 uc1 <+> BS ll2 lc2 ul2 uc2 =
    BS (min ll1 ll2) (min lc1 lc2) (max ul1 ul2) (max uc1 uc2)

public export
Monoid Bounds where
  neutral = NoBounds

public export
record Bounded ty where
  constructor BD
  val    : ty
  bounds : Bounds

%runElab derive "Bounded" [Show,Eq]

public export
bounded : a -> (lstart,cstart,lstop,cstop : Nat) -> Bounded a
bounded v w x y z = BD v $ BS w x y z

public export %inline
oneChar : a -> (l,c : Nat) -> Bounded a
oneChar v l c = bounded v l c l (S c)

public export
app : Bounded (a -> b) -> Bounded a -> Bounded b
app (BD vf b1) (BD va b2) = BD (vf va) (b1 <+> b2)

public export
bind : Bounded a -> (a -> Bounded b) -> Bounded b
bind (BD va b1) f =
  let BD vb b2 = f va
   in BD vb (b1 <+> b2)

public export
Functor Bounded where
  map f (BD val bs) = BD (f val) bs

public export %inline
Applicative Bounded where
  pure v = BD v neutral
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
  traverse f (BD v bs) = (`BD` bs) <$> f v
