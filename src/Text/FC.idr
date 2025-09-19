module Text.FC

import Data.ByteString
import Data.String
import Derive.Prelude
import Text.Bounds

%default total
%language ElabReflection

public export
data Origin : Type where
  FileSrc : (path : String) -> Origin
  Virtual : Origin

%runElab derive "Origin" [Show,Eq]

public export
Interpolation Origin where
  interpolate (FileSrc p) = p
  interpolate Virtual     = "virtual"

public export
record FileContext where
  constructor FC
  origin : Origin
  bounds : Bounds

public export %inline
fromBounded : Origin -> Bounded a -> (FileContext, a)
fromBounded o (B val bounds) = (FC o bounds, val)

public export %inline
virtualFromBounded : Bounded a -> (FileContext, a)
virtualFromBounded = fromBounded Virtual

%runElab derive "FileContext" [Show,Eq]

export
Interpolation FileContext where
  interpolate (FC o NoBounds) = interpolate o
  interpolate (FC o b)        = "\{o}: \{b}"

nextRem : Fin 4 -> Bits8 -> Fin 4
nextRem FZ     m =
  if      m < 0b1000_0000  then 0
  else if m < 0b1110_0000  then 1
  else if m < 0b1111_0000  then 2
  else                          3
nextRem (FS x) m = weaken x

||| Converts an index into a bytestring to a position
||| (line and column) in the corresponding UTF-8 string.
export
toPosition : Nat -> ByteString -> Position
toPosition n (BS x bv) = go 0 0 x 0
  where
    -- we iterate over a bytestring of UTF-8 encoded characters
    -- if we are in the middle of a character, we continue until
    -- the end of character is encountered.
    go : (l,c : Nat) -> (n : Nat) -> Fin 4 -> (y : Ix n x) => Position
    go l c 0     _   = P l c
    go l c (S k) rem =
      let byte := bv `ix` k
          nxt  := nextRem rem byte
       in case nxt of
            0 => case ixToNat y >= n of
              True  => P l c
              False => case byte of
                0x0a => go (l+1) 0     k nxt
                _    => go l     (c+1) k nxt
            _ => go l c k nxt

range : Nat -> Nat -> List a -> List a
range s e = take ((e `minus` s) + 1) . drop s

lineNumbers : SnocList String -> Nat -> Nat -> List String -> SnocList String
lineNumbers sl _ _    []     = sl
lineNumbers sl size n (h::t) =
  let k   := S n
      pre := padLeft size '0' $ show k
   in lineNumbers (sl :< " \{pre} | \{h}") size k t

||| Pretty prints a file context, highlighting the section in the given
||| list of source lines.
|||
||| The `FileContext` describes the absolute context (file source and
||| bounds) where an error occurred, while `relBounds` is the error's
||| position relative to the given list of lines.
|||
||| The above distinction is necessary when streaming large amounts of
||| data, where it is not feasible to keep the whole data in memory but
||| only the most recent chunk.
export
printFC :
     FileContext
  -> (relBounds   : Bounds)
  -> (sourceLines : List String)
  -> List String
printFC fc@(FC _ $ BS (P so _) (P eo _)) (BS (P sr sc) (P er ec)) ls =
  let  nsize  := length $ show (eo + 1)
       head   := "\{fc}"
   in case sr == er of
     False =>
       lineNumbers [<"",head] nsize so (range sr (min er $ sr+5) ls) <>> []
     True  =>
       let -- In case of end-of-input errors, we sometimes get `ec == sc`.
           -- We want to make sure we still print at least one emphasis character
           -- in those cases.
           cemph := max 1 $ ec `minus` sc
           emph  := indent (nsize + sc + 4) (replicate cemph '^')
           fr    := er `minus` 4 -- first row
           begin := so `minus` (er `minus` fr)
        in lineNumbers [<"",head] nsize begin (range fr er ls) <>> [emph]
printFC fc _ _  = [interpolate fc]
