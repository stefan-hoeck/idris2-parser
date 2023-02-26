module Text.WebIDL.Parser.Util

import public Data.Refined
import public Data.List.Elem
import public Text.Parse.Manual
import public Text.WebIDL.Types
import public Text.WebIDL.Lexer

export %inline
fromChar : Char -> IdlToken
fromChar c = Other $ Symb c

export %inline
fromString : (v : String) -> {auto 0 p : Holds IsKeyword v} -> IdlToken
fromString v = Key $ MkKeyword v p

public export
0 AccRule : Bool -> Type -> Type
AccRule b a =
     (ts : List (Bounded IdlToken))
  -> (0 acc : SuffixAcc ts)
  -> Res b IdlToken ts ParseErr a

public export
0 Rule : Bool -> Type -> Type
Rule b a = (ts : List (Bounded IdlToken)) -> Res b IdlToken ts ParseErr a
