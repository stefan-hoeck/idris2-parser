module Text.TOML.Lexer

import Data.Time.Time
import Data.List1
import Data.SnocList
import Text.Parse.Manual
import Text.Time.Lexer
import Text.TOML.Types

%default total

-- facilitates pattern matching on and creating of symbol
-- tokens such as "[". We don't want to export this, as it tends
-- to interfer with regular `String` literals.
%inline
fromString : String -> TomlToken
fromString = TSym

--------------------------------------------------------------------------------
--          Keys
--------------------------------------------------------------------------------

isKeyChar : Char -> Bool
isKeyChar '-' = True
isKeyChar '_' = True
isKeyChar c   = isAlphaNum c

key : SnocList Char -> AutoTok e String
key sc (x::xs) =
  if isKeyChar x then key (sc :< x) xs else Succ (cast sc) (x::xs)
key sc []        = Succ (cast sc) []

--------------------------------------------------------------------------------
--          String literals
--------------------------------------------------------------------------------

MaxChar,LowerInvalid,UpperInvalid : Nat
MaxChar      = 0x10FFFF
LowerInvalid = 0xD800
UpperInvalid = 0xDFFF

-- try to read a sequence of hexadecimal digits
tryHex : Nat -> List Char -> Maybe Char
tryHex k []        =
  if k <= MaxChar && (k < LowerInvalid || k > UpperInvalid) then Just $ cast k
  else Nothing
tryHex k (x :: xs) = case isHexDigit x of
  True  => tryHex (k*16 + hexDigit x) xs
  False => Nothing

commentControl : Char -> Bool
commentControl '\127' = True
commentControl x      = x <= '\8' || (x >= '\10' && x <= '\31')

tomlControl : Char -> Bool
tomlControl '\n' = True
tomlControl '\f' = True
tomlControl '\b' = True
tomlControl '\r' = True
tomlControl '\t' = True
tomlControl x    = commentControl x

-- reads and unescapes a plain string
str : SnocList Char -> AutoTok e String
str sc ('\\' :: c  :: xs) = case c of
  '"'  => str (sc :< '"') xs
  'n'  => str (sc :< '\n') xs
  'f'  => str (sc :< '\f') xs
  'b'  => str (sc :< '\b') xs
  'r'  => str (sc :< '\r') xs
  't'  => str (sc :< '\t') xs
  '\\' => str (sc :< '\\') xs
  'u'  => case xs of
    w::x::y::z::t' => case tryHex 0 [w,x,y,z] of
      Just c => str (sc :< c) t'
      Nothing => invalidEscape p t'
    _    => invalidEscape p xs
  'U'  => case xs of
    s::t::u::v::w::x::y::z::t' => case tryHex 0 [s,t,u,v,w,x,y,z] of
      Just c => str (sc :< c) t'
      Nothing => invalidEscape p t'
    _    => invalidEscape p xs
  _    => invalidEscape p (c::xs)
str sc ('"'  :: xs) = Succ (cast sc) xs
str sc (c    :: xs) =
  if tomlControl c then range (InvalidControl c) p xs
  else str (sc :< c) xs
str sc []           = eoiAt p

validTrim : List Char -> Bool
validTrim ('\t' :: xs)     = validTrim xs
validTrim (' ' :: xs)      = validTrim xs
validTrim ('\n' :: xs)     = True
validTrim ('\r'::'\n'::xs) = True
validTrim _ = False

-- reads and unescapes a multi-line string
strML : (trim : Bool) -> SnocList Char -> AutoTok e String
strML trim sc ('\\' :: c  :: xs) = case c of
  '"'  => strML False (sc :< '"') xs
  'n'  => strML False (sc :< '\n') xs
  'f'  => strML False (sc :< '\f') xs
  'b'  => strML False (sc :< '\b') xs
  'r'  => strML False (sc :< '\r') xs
  't'  => strML False (sc :< '\t') xs
  '\\' => strML False (sc :< '\\') xs
  'u'  => case xs of
    w::x::y::z::t' => case tryHex 0 [w,x,y,z] of
      Just c => strML False (sc :< c) t'
      Nothing => invalidEscape p t'
    _    => invalidEscape p xs
  'U'  => case xs of
    s::t::u::v::w::x::y::z::t' => case tryHex 0 [s,t,u,v,w,x,y,z] of
      Just c => strML False (sc :< c) t'
      Nothing => invalidEscape p t'
    _    => invalidEscape p xs
  _    => if validTrim (c::xs) then strML True sc xs
          else invalidEscape p (c::xs)
strML trim sc ('"'::'"'::'"'::'"'::'"'::xs) = Succ (cast $ sc :< '"' :< '"') xs
strML trim sc ('"'::'"'::'"'::'"'::xs) = Succ (cast $ sc :< '"') xs
strML trim sc ('"'::'"'::'"'::xs) = Succ (cast sc) xs
strML trim sc ('\n'::cs) =
  if trim then strML trim sc cs else strML trim (sc :< '\n') cs
strML trim sc ('\t'::cs) =
  if trim then strML trim sc cs else strML trim (sc :< '\t') cs
strML trim sc ('\r'::'\n'::cs) =
  if trim then strML trim sc cs else strML trim (sc :< '\r' :< '\n') cs
strML trim sc (c            ::xs) =
  if tomlControl c then range (InvalidControl c) p xs
  else if isSpace c && trim then strML trim sc xs
  else strML False (sc :< c) xs
strML trim sc []           = eoiAt p

-- reads a literal stirng
literal : SnocList Char -> AutoTok e String
literal sc ('\''::cs) = Succ (cast sc) cs
literal sc (c :: cs)  =
  if tomlControl c && c /= '\t' then range (InvalidControl c) p cs
  else literal (sc :< c) cs
literal sc [] = eoiAt p

-- reads a literal multi-line stirng
literalML : SnocList Char -> AutoTok e String
literalML sc ('\''::'\''::'\''::'\''::'\''::cs) = Succ (cast $ sc :< '\'' :< '\'') cs
literalML sc ('\''::'\''::'\''::'\''::cs) = Succ (cast $ sc :< '\'') cs
literalML sc ('\''::'\''::'\''::cs) = Succ (cast sc) cs
literalML sc ('\n'::cs) = literalML (sc :< '\n') cs
literalML sc ('\r'::'\n'::cs) = literalML (sc :< '\r' :< '\n') cs
literalML sc (c :: cs)  =
  if tomlControl c && c /= '\t' then range (InvalidControl c) p cs
  else literalML (sc :< c) cs
literalML sc [] = eoiAt p

-------------------------------------------------------------------------------
--          Numeric literals
-------------------------------------------------------------------------------

-- converts an integer literal
intLit : SnocList Char -> (res,pow : Nat) -> TomlToken
intLit [<]       res _   = TVal (TInt $ cast res)
intLit [<'-']    res _   = TVal (TInt . negate $ cast res)
intLit (sx :< x) res pow = intLit sx (res + pow * digit x) (pow * 10)

-- converts a floating point literal
dblLit : SnocList Char -> TomlToken
dblLit sc = 
  if any (\c => '.' == c || 'e' == c) sc
     then TVal . TDbl . Float . cast $ cast {to = String} sc
     else intLit sc 0 1

num',rest,dot,exp,digs,digs1 : SnocList Char -> AutoTok e TomlToken

-- addditional exponent digits, possibly separated by underscores
digs sc ('_'::x::xs) =
  if isDigit x then digs (sc:<x) xs else unknownRange p xs
digs sc (x::xs)      =
  if isDigit x then digs (sc:<x) xs else Succ (dblLit sc) (x::xs)
digs sc []           = Succ (dblLit sc) []

-- mandatory exponent digits, possibly separated by underscores
digs1 sc (x :: xs) = if isDigit x then digs (sc:<x) xs else unknown p
digs1 sc []        = eoiAt p

-- exponent: 'e' or 'E' followed by optional '+' or '-' and
-- at least one decimal digit
exp sc ('e'::'+'::xs) = digs1 (sc:<'e') xs
exp sc ('E'::'+'::xs) = digs1 (sc:<'e') xs
exp sc ('e'::'-'::xs) = digs1 (sc:<'e':<'-') xs
exp sc ('E'::'-'::xs) = digs1 (sc:<'e':<'-') xs
exp sc ('e'::xs)      = digs1 (sc:<'e') xs
exp sc ('E'::xs)      = digs1 (sc:<'e') xs
exp sc xs             = Succ (dblLit sc) xs

-- digits after the decimal dot, possibly separated by '_'
dot sc ('_'::x::xs) = if isDigit x then dot (sc:<x) xs else unknownRange p xs
dot sc (x::xs)      = if isDigit x then dot (sc:<x) xs else exp sc (x::xs)
dot sc []           = Succ (dblLit sc) []

-- optional decimal and exponent part.
rest sc ('.'::x::xs) = if isDigit x then dot (sc:<'.':< x) xs else unknown p
rest sc ('.'::[])    = unknown p
rest sc xs           = exp sc xs

-- lexes an integer or floating point literal
num' sc ('_'::x::xs) = if isDigit x then num' (sc:<x) xs else unknownRange p xs
num' sc (x::xs)      = if isDigit x then num' (sc:<x) xs else rest sc (x::xs)
num' sc []           = Succ (intLit sc 0 1) []

num : Tok e TomlToken
num ('-'::'0'::t) = rest [<'-','0'] t
num ('+'::'0'::t) = rest [<'0'] t
num ('-'::d::t)   = if isDigit d then num' [<'-',d] t else unknownRange Same t
num ('+'::d::t)   = if isDigit d then num' [<d] t else unknown Same
num ('0'::t)      = rest [<'0'] t
num (d::t)        = if isDigit d then num' [<d] t else unknown Same
num []            = eoiAt Same

--------------------------------------------------------------------------------
--          Misc.
--------------------------------------------------------------------------------

comment : AutoTok e TomlToken
comment []           = Succ Comment []
comment ('\n' :: xs) = Succ Comment ('\n' :: xs)
comment ('\r' :: xs) = Succ Comment ('\r' :: xs)
comment ('\t' :: xs) = comment xs
comment (x :: xs)            =
  if commentControl x then range (InvalidControl x) p xs else comment xs

validSpace : Char -> Bool
validSpace ' '  = True
validSpace '\n' = True
validSpace '\t' = True
validSpace _    = False

space : AutoTok e TomlToken
space ('\r'::'\n'::xs) = space xs
space (x::xs)          = if validSpace x then space xs else Succ Space (x::xs)
space []               = Succ Space []

--------------------------------------------------------------------------------
--          Single-step lexers
--------------------------------------------------------------------------------

isTime : List Char -> Bool
isTime (_::_::':'::_)       = True
isTime (_::_::_::_::'-'::_) = True
isTime _                    = False

isNum : List Char -> Bool
isNum ('-'::_) = True
isNum ('+'::_) = True
isNum (d::_)   = isDigit d
isNum []       = False

-- general lexemes that can occur in key and value contexts
other : Tok e TomlToken
other ('.'  :: xs) = Succ "." xs
other (','  :: xs) = Succ "," xs
other ('='  :: xs) = Succ "=" xs
other ('[' :: xs)  = Succ "[" xs
other (']' :: xs)  = Succ "]" xs
other ('}' :: xs)  = Succ "}" xs
other ('#' :: xs)  = comment xs
other ('\r'::'\n'::xs) = space xs
other (x   :: xs)  = if validSpace x then space xs else unknown Same
other []           = eoiAt Same

toKey : Position -> KeyType -> LexRes cs e String -> LexRes cs e TomlToken
toKey x t (Succ v xs @{p}) = Succ (key1 $ KT v t $ BS x (move x p)) xs
toKey _ _ (Fail x y z)     = Fail x y z

-- lexes a key or sequence of dot-separated keys
-- this includes double brackets for table arrays
anyKey : Position -> Tok e TomlToken
anyKey pos ('"'  :: xs) = toKey pos Quoted $ str [<] xs
anyKey pos ('\'' :: xs) = toKey pos Literal $ literal [<] xs
anyKey pos ('['::'[':: xs) = Succ "[[" xs
anyKey pos (']'::']':: xs) = Succ "]]" xs
anyKey pos (x :: xs)    =
  if isKeyChar x then toKey pos Plain (key [<x] xs) else other (x::xs)
anyKey _   xs           = other xs

-- lexes a value or related symbol
val : Tok e TomlToken
val ('{' :: xs)                   = Succ "{" xs
val ('"' :: '"' :: '"' :: xs)     = case xs of
  '\n'::t         => TVal . TStr <$> strML False [<] t
  '\r' :: '\n'::t => TVal . TStr <$> strML False [<] t
  _               => TVal . TStr <$> strML False [<] xs
val ('\'' :: '\'' :: '\'' :: xs)     = case xs of
  '\n'::t         => TVal . TStr <$> literalML [<] t
  '\r' :: '\n'::t => TVal . TStr <$> literalML [<] t
  _               => TVal . TStr <$> literalML [<] xs
val ('"' :: xs)                   = TVal . TStr <$> str [<] xs
val ('\'' :: xs)                  = TVal . TStr <$> literal [<] xs
val ('0'::'x':: xs)               = TVal . TInt . cast <$> hexSep xs
val ('0'::'b':: xs)               = TVal . TInt . cast <$> binSep xs
val ('0'::'o':: xs)               = TVal . TInt . cast <$> octSep xs
val ('t'::'r'::'u'::'e'::xs)      = Succ (TVal $ TBool True) xs
val ('f'::'a'::'l'::'s'::'e'::xs) = Succ (TVal $ TBool False) xs
val ('n'::'a'::'n'::xs)           = Succ (TVal $ TDbl NaN) xs
val ('+'::'n'::'a'::'n'::xs)      = Succ (TVal $ TDbl NaN) xs
val ('-'::'n'::'a'::'n'::xs)      = Succ (TVal $ TDbl NaN) xs
val ('i'::'n'::'f'::xs)           = Succ (TVal $ TDbl $ Infty Nothing) xs
val ('+'::'i'::'n'::'f'::xs)      = Succ (TVal $ TDbl $ Infty $ Just Plus) xs
val ('-'::'i'::'n'::'f'::xs)      = Succ (TVal $ TDbl $ Infty $ Just Minus) xs
val cs =
  (TVal . TTime <$> anyTime cs) <|> num cs <|> other cs

--------------------------------------------------------------------------------
--          State
--------------------------------------------------------------------------------

-- In TOML files, we are either in a position where a (sequence of)
-- keys is expected, or in a position, where a value is expected.
-- This tag keeps track of the two possible contexts.
data Ctxt = Key | Value

-- Current state of the lexer: Keeps track of whether we are at
-- the toplevel, or in a nesting of arrays and/or literal tables.
-- Depending on the current state, we run one of two possible
-- lexers, the result of which affects the next state.
data LexState : Ctxt -> Type where
  TopLevel : {0 t : Ctxt} -> LexState t
  InArray  : (outer : LexState Value) -> LexState Value
  InTable  : {0 t : Ctxt} -> (outer : LexState Value) -> LexState t

-- after encountering an equals sign (`'='`) we switch from
-- `Key` to `Value` context.
switch : LexState Key -> LexState Value
switch TopLevel        = TopLevel
switch (InTable outer) = InTable outer

adjState : (t : Ctxt) -> TomlToken -> LexState t -> (t2 ** LexState t2)
adjState Key  "="  outer           = (_ ** switch outer)
adjState Value NL  TopLevel        = (Key ** TopLevel)
adjState Value "]" (InArray outer) = (_ ** outer)
adjState _     "}" (InTable outer) = (_ ** outer)
adjState Value "[" outer           = (_ ** InArray outer)
adjState Value "{" outer           = (Key ** InTable outer)
adjState Value "," (InTable outer) = (Key ** InTable outer)
adjState t     _   st              = (t ** st)

-- decides on the lexer to run depending on the current
-- context
%inline
anyTok : Position -> Ctxt -> Tok e TomlToken
anyTok pos Key   = anyKey pos
anyTok _   Value = val

-- We convert a `Space` token to a `NL` if the sequence of
-- spaces contains a line break and we are not in an array
-- literal (where arbitrary line breaks are allowed).
adjSpace : LexState c -> (hasNL : Bool) -> TomlToken -> Maybe TomlToken
adjSpace TopLevel    True Space   = Just NL
adjSpace (InTable _) True Space   = Just NL
adjSpace _           _    Space   = Nothing
adjSpace _           _    Comment = Nothing
adjSpace _           _    t       = Just t

--------------------------------------------------------------------------------
--          Post Processing
--------------------------------------------------------------------------------

-- to simplify the parser, we group paths of dot-separated key in
-- a single pass when converting the `SnocList` of tokens to
-- a list of tokens.
groupKeys :
     List (Bounded TomlToken)
  -> Bounded (List1 KeyToken)
  -> SnocList (Bounded TomlToken)
  -> List (Bounded TomlToken)

-- to simplify the parser, we remove non-relevant tokens in
-- a single pass when converting the `SnocList` of tokens to
-- a list of tokens.
postProcess :
     List (Bounded TomlToken)
  -> SnocList (Bounded TomlToken)
  -> List (Bounded TomlToken)

groupKeys ts ks (sx :< B (TKey p) bk :< B "." bd) =
  groupKeys ts (B (p <+> ks.val) (ks.bounds <+> bd <+> bk)) sx
groupKeys ts ks sx = postProcess (map TKey ks :: ts) sx

postProcess ts [<]       = ts
postProcess ts (sx :< x) = case x.val of
  TKey s  => groupKeys ts (x $> s) sx
  Comment => postProcess ts sx
  _       => postProcess (x::ts) sx

--------------------------------------------------------------------------------
--          Complete Lexer
--------------------------------------------------------------------------------

lex :
     {t : Ctxt}
  -> LexState t
  -> Position
  -> SnocList (Bounded TomlToken)
  -> (cs : List Char)
  -> (0 acc : SuffixAcc cs)
  -> Either (Bounded TomlErr) (List $ Bounded TomlToken)
lex st pos sx [] _      = Right $ postProcess [] sx
lex st pos sx xs (SA r) = case anyTok pos t xs of
  Succ val ys @{p@(Uncons _)} =>
    let pos2        := endPos pos p
        Just v      := adjSpace st (pos2.line > pos.line) val
          | Nothing => lex st pos2 sx ys r
        (t2 ** st2) := adjState t v st
     in lex st2 pos2 (sx :< bounded v pos pos2) ys r
  Succ _ _ => Left $ oneChar NoConsumption pos
  Fail start errEnd y => Left $ boundedErr pos start errEnd (voidLeft y)

export %inline
lexToml : String -> Either (Bounded TomlErr) (List $ Bounded TomlToken)
lexToml s = lex {t = Key} TopLevel begin [<] (unpack s) suffixAcc
