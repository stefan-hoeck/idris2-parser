module Gen.String

import public Gen.Util

--------------------------------------------------------------------------------
--          String
--------------------------------------------------------------------------------

simple : Gen String
simple = linString 10 printableUnicode

encodeSimple : SnocList Char -> List Char -> String
encodeSimple sc [] = pack $ sc <>> ['"']
encodeSimple sc ('"' :: xs) = encodeSimple (sc :< '\\' :< '"') xs
encodeSimple sc (x :: xs) = encodeSimple (sc :< x) xs

export
encodedString : Gen (Encoded String)
encodedString = map (\s => Enc (encodeSimple [<'"'] $ unpack s) s) simple
