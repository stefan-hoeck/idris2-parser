module Text.FC

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

range : Nat -> Nat -> List a -> List a
range s e = take ((e `minus` s) + 1) . drop s

lineNumbers : SnocList String -> Nat -> Nat -> List String -> SnocList String
lineNumbers sl _ _    []     = sl
lineNumbers sl size n (h::t) =
  let k   := S n
      pre := padLeft size '0' $ show k
   in lineNumbers (sl :< " \{pre} | \{h}") size k t

export
printFC : FileContext -> (sourceLines : List String) -> List String
printFC fc ls = case fc.bounds of
  NoBounds       => []
  BS (P sr sc) (P er ec) =>
    let  nsize  := length $ show (er + 1) 
         head   := "\{fc}"
     in case sr == er of
       False =>
         lineNumbers [<"",head] nsize sr (range sr (min er $ sr+5) ls) <>> []
       True  =>
         let emph := indent (nsize + sc + 4) (replicate (ec `minus` sc) '^')
             fr   := er `minus` 4 -- first row
          in lineNumbers [<"",head] nsize fr (range fr er ls) <>> [emph]
