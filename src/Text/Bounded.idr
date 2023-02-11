module Text.Bounded

import Data.List.Suffix
import Derive.Prelude

%default total

%language ElabReflection

public export
record Position where
  [noHints]
  constructor P
  line : Nat
  col  : Nat

public export
begin : Position
begin = P 0 0

public export %inline
incCol : Position -> Position
incCol = {col $= S}

public export %inline
incLine : Position -> Position
incLine p = P (S p.line) 0

public export %inline
addCol : Nat -> Position -> Position
addCol n = {col $= (+ n)}

%runElab derive "Position" [Show,Eq,Ord]

public export
Interpolation Position where
  interpolate (P l c) = show (l+1) ++ ":" ++ show (c+1)

public export
data Bounds : Type where
  BS : (start, end : Position) -> Bounds
  NoBounds : Bounds

%runElab derive "Bounds" [Show,Eq]

namespace Bounds
  public export
  oneChar : Position -> Bounds
  oneChar p = BS p $ incCol p

export
Interpolation Bounds where
  interpolate (BS s e) = "\{s}--\{e}"
  interpolate NoBounds = ""

public export
Semigroup Bounds where
  NoBounds <+> y        = y
  x        <+> NoBounds = x
  BS s1 e1 <+> BS s2 e2 = BS (min s1 s2) (max e1 e2)

public export
Monoid Bounds where
  neutral = NoBounds

public export
record Bounded ty where
  constructor B
  val    : ty
  bounds : Bounds

%runElab derive "Bounded" [Show,Eq]

public export
bounded : a -> (start,end : Position) -> Bounded a
bounded v s e = B v $ BS s e

public export %inline
oneChar : a -> Position -> Bounded a
oneChar v p = B v $ oneChar p

public export
app : Bounded (a -> b) -> Bounded a -> Bounded b
app (B vf b1) (B va b2) = B (vf va) (b1 <+> b2)

public export
bind : Bounded a -> (a -> Bounded b) -> Bounded b
bind (B va b1) f =
  let B vb b2 = f va
   in B vb (b1 <+> b2)

public export
Functor Bounded where
  map f (B val bs) = B (f val) bs

public export %inline
Applicative Bounded where
  pure v = B v neutral
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
  traverse f (B v bs) = (`B` bs) <$> f v

--------------------------------------------------------------------------------
--          Suffix Res
--------------------------------------------------------------------------------

calcEnd : (line,col : Nat) -> (cs : List Char) -> Suffix b ys cs -> Position
calcEnd l c ys          Same       = P l c
calcEnd l c ('\n' :: t) (Uncons x) = calcEnd (S l) 0 t (unconsBoth x)
calcEnd l c (_    :: t) (Uncons x) = calcEnd l (S c) t (unconsBoth x)
calcEnd l c []          (Uncons x) = absurd x

export %inline
endPos :
     {cs : List Char}
  -> (pos : Position)
  -> Suffix b ys cs
  -> Position
endPos pos = calcEnd pos.line pos.col cs

export
boundedErr :
     {0 e : Type}
  -> {ts,errStart : List Char}
  -> Position
  -> (start : Suffix False errStart ts)
  -> (0 errEnd : List Char)
  -> {auto end : Suffix False errEnd errStart}
  -> (err : e)
  -> Bounded e
boundedErr pos start errEnd err =
  let ps := endPos pos start
      pe := endPos ps end
   in bounded err ps pe
