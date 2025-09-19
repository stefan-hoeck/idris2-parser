module Text.Bounds

import Data.Bits
import Data.ByteString
import Data.List.Shift
import Data.List.Suffix
import Derive.Prelude

%default total

%language ElabReflection

--------------------------------------------------------------------------------
--          Position
--------------------------------------------------------------------------------

||| Position in a string as a pair of natural numbers.
||| Both numbers are zero-based.
public export
record Position where
  [noHints]
  constructor P
  ||| The current line in a string (0-based)
  line : Nat
  ||| The current column in a string (0-based)
  col  : Nat

||| The beginning of a string. This is an alias for `P 0 0`.
public export
begin : Position
begin = P 0 0

||| Increase the current column by one.
public export %inline
incCol : Position -> Position
incCol = {col $= S}

||| Increase the current line by one, resetting the
||| column to 0.
public export %inline
incLine : Position -> Position
incLine p = P (S p.line) 0

||| Increase the current column by the given number of steps.
public export %inline
addCol : Nat -> Position -> Position
addCol n = {col $= (+ n)}

||| Computes `p2` relative to `p1`, that is, given an earlier
||| position `p1`, returns the number of lines and columns
||| necessary to advance from `p1` to `p2`.
export
relativeTo : (p2,p1 : Position) -> Position
relativeTo (P l c) (P ls cs) =
  if l <= ls then P 0 (c `minus` cs) else P (l `minus` ls) c

||| Advances the given text position by the characters encountered
||| in the given string.
|||
||| A line feed character ('\n'; codepoint `0x0A`) will increase
||| the current line by one and reset the column to zero. Every
||| other character will increase the column by one.
export
incString : String -> Position -> Position
incString s (P l c) = go l c (unpack s)
  where
    go : Nat -> Nat -> List Char -> Position
    go l c []        = P l c
    go l c ('\n' :: xs) = go (S l) 0 xs
    go l c (x    :: xs) = go l (S c) xs

||| Advances the given text position by the bytes encountered
||| in the given string.
|||
||| A line feed byte (`0x0A`) will increase
||| the current line by one and reset the column to zero. Every
||| other start character of a unicode code point will advance
||| the column by one.
export
incBytes : ByteString -> Position -> Position
incBytes (BS n bv) (P l c) = go l c n
  where
    go : Nat -> Nat -> (k : Nat) -> (x : Ix k n) => Position
    go l c 0     = P l c
    go l c (S k) =
      case bv `ix` k of
        0x0a => go (S l) 0 k
        b    => case b < 128 || b .&. 0b1100_0000 == 0b1100_000 of
          True => go l (S c) k
          _    => go l c k

||| Shift the position by a number of columns represented by
||| a `Shift` value. This assumes, that no line break was "shifted".
public export %inline
shift : Position -> Shift b t sx xs sy ys -> Position
shift p s = addCol (toNat s) p

||| Shift the position by a number of columns represented by
||| a `Suffix` value. This assumes, that no line break was "shifted".
public export %inline
move : Position -> Suffix b xs ys -> Position
move p s = addCol (toNat s) p

||| Adjusts the current position by one character.
|||
||| If the character is a line break, a new line will be strated and
||| the column set to zero, otherwise, the column is increase by one.
public export %inline
next : Char -> Position -> Position
next '\n' = incLine
next _    = incCol

%runElab derive "Position" [Show,Eq,Ord]

public export
Interpolation Position where
  interpolate (P l c) = show (l+1) ++ ":" ++ show (c+1)

--------------------------------------------------------------------------------
--          Bounds
--------------------------------------------------------------------------------

||| A pair of `Position`s, describing a text range, or `NoBounds` for
||| use - for instance - with programmatically created tokens.
public export
data Bounds : Type where
  BS : (start, end : Position) -> Bounds
  NoBounds : Bounds

%runElab derive "Bounds" [Show,Eq]

namespace Bounds
  ||| Convert a single `Position` to a range one character wide.
  public export %inline
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

--------------------------------------------------------------------------------
--          Bounded
--------------------------------------------------------------------------------

||| Pairs a value with the textual bounds from where it was parsed.
public export
record Bounded ty where
  constructor B
  val    : ty
  bounds : Bounds

%runElab derive "Bounded" [Show,Eq]

||| Smart costructor for `Bounded`.
public export
bounded : a -> (start,end : Position) -> Bounded a
bounded v s e = B v $ BS s e

||| Smart costructor for `Bounded`.
public export %inline
oneChar : a -> Position -> Bounded a
oneChar v p = B v $ oneChar p

||| Implementation of `(<*>)`
public export
app : Bounded (a -> b) -> Bounded a -> Bounded b
app (B vf b1) (B va b2) = B (vf va) (b1 <+> b2)

||| Implementation of `(>>=)`
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

||| Calculates the new position from a `Suffix` by reinspecting
||| the original list of characters.
||| 
||| Use this, if the consumed prefix might have contained line breaks.
||| Otherwise, consider using `move`, which runs in O(1) instead of O(n).
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
