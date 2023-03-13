module Gen.Util

import Derive.Prelude
import public Data.List1
import public Data.String
import public Data.Vect
import public Hedgehog
import public Text.TOML.Types

%default total
%language ElabReflection

public export
record Encoded a where
  constructor Enc
  code  : String
  value : a

public export
Functor Encoded where
  map f (Enc c v) = Enc c $ f v

%runElab derive "Encoded" [Show,Eq]

public export
encoded : (a -> String) -> Gen a -> Gen (Encoded a)
encoded f = map $ \v => Enc (f v) v

--------------------------------------------------------------------------------
--          Lists
--------------------------------------------------------------------------------

export %inline
linList : Nat -> Gen a -> Gen (List a)
linList = list . linear 0

export %inline
linList1 : Nat -> Gen a -> Gen (List a)
linList1 = list . linear 1

export %inline
linString : Nat -> Gen Char -> Gen String
linString n = map pack . linList n

export %inline
linString1 : Nat -> Gen Char -> Gen String
linString1 n = map pack . linList1 n

--------------------------------------------------------------------------------
--          Comment
--------------------------------------------------------------------------------

isCommentControl : Char -> Bool
isCommentControl c =
  let n := the Nat $ cast c
   in n <= 0x8 || (n >= 0xa && n <= 0x1f) || n == 0x7f

-- from the spec
-- Control characters other than tab (U+0000 to U+0008,
-- U+000A to U+001F, U+007F) are not permitted in comments.
export
comment : Gen String
comment = ("#" ++) <$> linString 10 (map toCommentChar unicode)
  where toCommentChar : Char -> Char
        toCommentChar c = if isCommentControl c then ' ' else c

--------------------------------------------------------------------------------
--          Space
--------------------------------------------------------------------------------

export
lineSpace : Gen String
lineSpace = linString 3 (element [' ', '\t'])

export
anySpace : Gen String
anySpace = linString 3 (element [' ', '\t', '\n'])

-- encodes a value with arbitrary whitespace before and
-- after, but without line breaks
export
spaced : Gen (Encoded a) -> Gen (Encoded a)
spaced g = [| adj lineSpace g lineSpace |]
  where
    adj : String -> Encoded a -> String -> Encoded a
    adj s1 (Enc c v) s2 = Enc (s1 ++ c ++ s2) v

-- Encodes a value with arbitrary whitespace before and
-- after.
-- In addition, the value can be followed by a comment plus
-- line break or a line break.
export
spacedNL : Gen (Encoded a) -> Gen (Encoded a)
spacedNL g = [| adj lineSpace g anySpace (maybe comment) anySpace |]
  where
    adj : String -> Encoded a -> String -> Maybe String -> String -> Encoded a
    adj s1 (Enc c v) s2 mc s3 = Enc (s1 ++ c ++ maybe s2 (++ "\n") mc ++ s3) v
