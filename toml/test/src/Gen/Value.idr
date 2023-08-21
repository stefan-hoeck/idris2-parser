module Gen.Value

import public Gen.Bool
import public Gen.Float
import public Gen.Int
import public Gen.Key
import public Gen.String
import public Gen.Time

%default total

export
primVal : Gen (Encoded TomlValue)
primVal = frequency
  [ (1, bool)
  , (5, map TInt <$> encodedInteger)
  , (5, map TStr <$> encodedString)
  , (5, map TTime <$> anyTime)
  , (5, map TDbl <$> encodedFloat)
  ]

export
value, array : Nat -> Gen (Encoded TomlValue)

value 0 = primVal
value (S k) = frequency [(1, primVal), (3, array k)]

array n = arr <$> linList 10 (spacedNL $ value n)

  where
    arr : List (Encoded TomlValue) -> Encoded TomlValue
    arr evs =
      let vs := map value evs
          cd := "[" ++ concat (intersperse "," $ map code evs) ++ "]"
       in Enc cd (TArr Static ([<] <>< vs))

export
keyVal : Gen (Encoded a) -> Gen (Encoded (Key, a))
keyVal val = [| acc (spaced key) (spaced val) |]

  where
    acc : Encoded Key -> Encoded a -> Encoded (Key,a)
    acc k v = Enc (k.code ++ "=" ++ v.code) (k.value,v.value)

export
keyValTbl : Gen (Encoded TomlValue) -> Gen (Encoded TomlValue)
keyValTbl val = map toTable <$> keyVal val

  where
    toTable : (Key,TomlValue) -> TomlValue
    toTable (k,v) = TTbl Table $ singleton k.head (go k.tail)

      where
        go : List String -> TomlValue
        go []        = v
        go (x :: xs) = TTbl None $ singleton x (go xs)
