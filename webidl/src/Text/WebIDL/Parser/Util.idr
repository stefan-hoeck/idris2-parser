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
  -> Res b IdlToken ts IdlError a

public export
0 Rule : Bool -> Type -> Type
Rule b a = (ts : List (Bounded IdlToken)) -> Res b IdlToken ts IdlError a

idlErr : Bounds -> IdlError -> Res b IdlToken ts IdlError a
idlErr b err = custom b err

public export
isOpen : IdlToken -> Bool
isOpen '(' = True
isOpen '[' = True
isOpen '{' = True
isOpen _   = False

public export
closes : IdlToken -> IdlToken -> Bool
')' `closes` '(' = True
']' `closes` '[' = True
'}' `closes` '{' = True
_   `closes` _   = False

public export
ident : Rule True Identifier
ident = terminal $ \case Ident i => Just i; _ => Nothing

public export %inline
inj :
      {0 a  : Type}
   -> {0 xs : List Type}
   -> Result0 b t ts e a
   -> {auto   p : Elem a xs}
   -> Result0 b t ts e (NS I xs)
inj r = map (\v => inject v) r
