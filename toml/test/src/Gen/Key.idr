module Gen.Key

import public Gen.Util

%default total

export
bareKey : Gen (Encoded String)
bareKey = (\s => Enc s s) <$> linString1 10 keyChar
  where keyChar : Gen Char
        keyChar = choice [alphaNum, element ['-', '_']]

export
singleKey : Gen (Encoded String)
singleKey = bareKey

||| Several keys separated by dots
export
key : Gen (Encoded Key)
key = [| acc (spaced singleKey) (linList 2 $ spaced singleKey) |]

  where
    acc : Encoded String -> List (Encoded String) -> Encoded Key
    acc k ks =
      Enc
        (concat . intersperse "." $ k.code :: map code ks)
        (k.value ::: map value ks)
