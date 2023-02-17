module Text.Parse.Manual

import public Data.Bool.Rewrite
import public Data.List.Shift
import public Data.List.Suffix
import public Data.List.Suffix.Result
import public Data.List.Suffix.Result0

import public Text.Bounds
import public Text.FC
import public Text.ParseError

import public Text.Lex.Manual
import public Text.Lex.Shift

public export
0 Res :
     (strict : Bool)
  -> (t : Type)
  -> (ts : List $ Bounded t)
  -> (e,a : Type)
  -> Type
Res b t ts e a = Result0 b (Bounded t) ts (Bounded $ ParseError t e) a
