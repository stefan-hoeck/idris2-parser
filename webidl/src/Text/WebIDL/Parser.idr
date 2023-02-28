module Text.WebIDL.Parser

import public Text.WebIDL.Parser.Arguments
import public Text.WebIDL.Parser.Attributes
import public Text.WebIDL.Parser.Definitions
import public Text.WebIDL.Parser.Members
import public Text.WebIDL.Parser.Type
import public Text.WebIDL.Parser.Util

--------------------------------------------------------------------------------
--          Parsing WebIDL
--------------------------------------------------------------------------------

export
parseIdl : Rule b a -> String -> Either (Bounded ParseErr) a
parseIdl g s =
  let Right ts := lexIdl s | Left err => Left err
      Succ0 v [] := g ts
        | Succ0 v (x::xs) => unexpected x
        | Fail0 err       => Left err
   in Right v
