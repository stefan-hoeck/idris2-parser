module LexJSON

import Derive.Prelude
import Text.Parse.Manual

%language ElabReflection
%default total

public export
data JSON : Type where
  JNull   : JSON
  JNumber : Double -> JSON
  JBool   : Bool   -> JSON
  JString : String -> JSON
  JArray  : List JSON -> JSON
  JObject : List (String, JSON) -> JSON

%runElab derive "JSON" [Show,Eq]

public export
data JSToken : Type where
  Symbol   : Char -> JSToken
  Lit      : JSON -> JSToken

%runElab derive "JSToken" [Show,Eq]

public export %inline
fromChar : Char -> JSToken
fromChar = Symbol

export
Interpolation JSToken where
  interpolate (Symbol c) = show c
  interpolate (Lit x)  = "'\{show x}'"

public export
data JSErr : Type where
  ExpectedString  : JSErr

%runElab derive "JSErr" [Show,Eq]

export
Interpolation JSErr where
  interpolate ExpectedString  = "Expected string literal"

public export %tcinline
0 JSParseErr : Type
JSParseErr = ParseError JSToken JSErr

strLit : SnocList Char -> JSToken
strLit = Lit . JString . cast

str : SnocList Char -> AutoTok Char JSToken
str sc ('\\' :: c  :: xs) = case c of
  '"'  => str (sc :< '"') xs
  'n'  => str (sc :< '\n') xs
  'f'  => str (sc :< '\f') xs
  'b'  => str (sc :< '\b') xs
  'r'  => str (sc :< '\r') xs
  't'  => str (sc :< '\t') xs
  '\\' => str (sc :< '\\') xs
  '/'  => str (sc :< '/') xs
  'u'  => case xs of
    w :: x :: y :: z :: t' =>
      if isHexDigit w && isHexDigit x && isHexDigit y && isHexDigit z
        then
          let c := cast $ hexDigit w * 0x1000 +
                          hexDigit x * 0x100 +
                          hexDigit y * 0x10 +
                          hexDigit z 
           in str (sc :< c) t'
        else invalidEscape p t'
    _    => invalidEscape p xs
  _    => invalidEscape p (c::xs)
str sc ('"'  :: xs) = Succ (strLit sc) xs
str sc (c    :: xs) = str (sc :< c) xs
str sc []           = failEOI p

export
tok : Tok Char JSToken
tok (','::xs)                    = Succ ',' xs
tok ('"'::xs)                    = str [<] xs
tok (':'::xs)                    = Succ ':' xs
tok ('['::xs)                    = Succ '[' xs
tok (']'::xs)                    = Succ ']' xs
tok ('{'::xs)                    = Succ '{' xs
tok ('}'::xs)                    = Succ '}' xs
tok ('n':: 'u'::'l'::'l'::t)     = Succ (Lit JNull) t
tok ('t'::'r'::'u'::'e'::t)      = Succ (Lit $ JBool True) t
tok ('f'::'a'::'l'::'s'::'e'::t) = Succ (Lit $ JBool False) t
tok xs                           = Lit . JNumber <$> double xs

export
lexJSON : String -> Either (Bounded StopReason) (List (Bounded JSToken))
lexJSON s = singleLineDropSpaces tok s
