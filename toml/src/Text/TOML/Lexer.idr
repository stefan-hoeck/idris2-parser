module Text.TOML.Lexer

import Data.SnocList
import Text.Parse.Manual
import Text.TOML.Types

%default total

%inline
fromChar : Char -> TomlToken
fromChar = TSym

--------------------------------------------------------------------------------
--          Keys
--------------------------------------------------------------------------------

toKey : SnocList Char -> TomlToken
toKey = TKey . pure . cast

isKeyChar : Char -> Bool
isKeyChar '-' = True
isKeyChar '_' = True
isKeyChar c   = isAlphaNum c

key : SnocList Char -> AutoTok Char TomlToken
key sc (x::xs) =
  if isKeyChar x then key (sc :< x) xs else Succ (toKey sc) (x::xs)
key sc []        = Succ (toKey sc) []

--------------------------------------------------------------------------------
--          String literals
--------------------------------------------------------------------------------

-- try to read a sequence of hexadecimal digits
tryHex : Nat -> List Char -> Maybe Char
tryHex k []        = Just $ cast k
tryHex k (x :: xs) = case isHexDigit x of
  True  => tryHex (k*16 + hexDigit x) xs
  False => Nothing

-- reads and unescapes a plain string
str : SnocList Char -> AutoTok Char String
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
  if isControl c then range (InvalidControl c) p xs
  else str (sc :< c) xs
str sc []           = failEOI p

-- reads a literal stirng
literal : SnocList Char -> AutoTok Char String
literal sc ('\''::cs) = Succ (cast sc) cs
literal sc (c :: cs)  =
  if isControl c && c /= '\t' then range (InvalidControl c) p cs
  else str (sc :< c) cs
literal sc [] = failEOI p

--------------------------------------------------------------------------------
--          Numeric literals
--------------------------------------------------------------------------------

-- converts an integer literal
intLit : SnocList Char -> (res,pow : Nat) -> TomlToken
intLit [<]       res _   = TVal (TNat res)
intLit [<'-']    res _   = TVal (TNeg res)
intLit (sx :< x) res pow = intLit sx (res + pow * digit x) (pow * 10)

-- converts a floating point literal
dblLit : SnocList Char -> TomlToken
dblLit sc = 
  if any (\c => '.' == c || 'e' == c) sc
     then TVal . TDbl . cast $ cast {to = String} sc
     else intLit sc 0 1

num,rest,dot,exp,digs,digs1 : SnocList Char -> AutoTok Char TomlToken

-- addditional exponent digits, possibly separated by underscores
digs sc ('_'::x::xs) = if isDigit x then digs (sc:<x) xs else unknown xs
digs sc (x::xs)      =
  if isDigit x then digs (sc:<x) xs else Succ (dblLit sc) (x::xs)
digs sc []           = Succ (dblLit sc) []

-- mandatory exponent digits, possibly separated by underscores
digs1 sc (x :: xs) = if isDigit x then digs (sc:<x) xs else unknown xs
digs1 sc []        = failEOI p

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
dot sc ('_'::x::xs) = if isDigit x then dot (sc:<x) xs else unknown xs
dot sc (x::xs)      = if isDigit x then dot (sc:<x) xs else exp sc (x::xs)
dot sc []           = Succ (dblLit sc) []

-- optional decimal and exponent part.
rest sc ('.'::x::xs) = if isDigit x then dot (sc:<'.':< x) xs else unknown xs
rest sc ('.'::[])    = unknown []
rest sc xs           = exp sc xs

-- lexes an integer or floating point literal
num sc ('_'::x::xs) = if isDigit x then num (sc:<x) xs else unknown xs
num sc (x::xs)      = if isDigit x then num (sc:<x) xs else rest sc (x::xs)
num sc []           = Succ (intLit sc 0 1) []

--------------------------------------------------------------------------------
--          Misc.
--------------------------------------------------------------------------------

comment : AutoTok Char TomlToken
comment []                   = Succ Comment []
comment ('\n' :: xs)         = Succ Comment ('\n' :: xs)
comment ('\r' :: '\n' :: xs) = Succ Comment ('\r' :: '\n' :: xs)
comment ('\t' :: xs)         = comment xs
comment (x :: xs)            =
  if isControl x then range (InvalidControl x) p xs else comment xs

validSpace : Char -> Bool
validSpace ' '  = True
validSpace '\n' = True
validSpace '\t' = True
validSpace '\r' = True
validSpace _    = False

space : AutoTok Char TomlToken
space (x::xs) = if validSpace x then space xs else Succ Space (x::xs)
space []      = Succ Space []

--------------------------------------------------------------------------------
--          Single-step lexers
--------------------------------------------------------------------------------

-- general lexemes that can occur in key and value contexts
other : Tok Char TomlToken
other ('.'  :: xs) = Succ '.' xs
other ('='  :: xs) = Succ '=' xs
other ('[' :: xs)  = Succ '[' xs
other (']' :: xs)  = Succ ']' xs
other ('#' :: xs)  = comment xs
other (x   :: xs)  = if validSpace x then space xs else unknown xs
other []           = failEmpty

-- lexes a key or sequence of dot-separated keys
anyKey : Tok Char TomlToken
anyKey ('"'  :: xs) = TKey . pure <$> str [<] xs
anyKey ('\'' :: xs) = TKey . pure <$> literal [<] xs
anyKey (x :: xs)    = if isKeyChar x then key [<x] xs else other (x::xs)
anyKey xs           = other xs

-- lexes a value or related symbol
val : Tok Char TomlToken
val ('{' :: xs)                   = Succ '{' xs
val ('}' :: xs)                   = Succ '}' xs
val (',' :: xs)                   = Succ ',' xs
val ('"' :: xs)                   = TVal . TStr <$> str [<] xs
val ('\'' :: xs)                  = TVal . TStr <$> literal [<] xs
val ('0'::'x':: xs)               = TVal . TNat <$> hexSep xs
val ('0'::'b':: xs)               = TVal . TNat <$> binSep xs
val ('0'::'o':: xs)               = TVal . TNat <$> octSep xs
val ('t'::'r'::'u'::'e'::xs)      = Succ (TVal $ TBool True) xs
val ('f'::'a'::'l'::'s'::'e'::xs) = Succ (TVal $ TBool False) xs
val ('+'::'0'::t) = rest [<'0'] t
val ('-'::'0'::t) = rest [<'-','0'] t
val ('+'::d::t)   = if isDigit d then num [<d] t else unknown t
val ('-'::d::t)   = if isDigit d then num [<'-',d] t else unknown t
val ('0'::t)      = rest [<'0'] t
val (d::t)        = if isDigit d then num [<d] t else other (d::t)
val []            = failEmpty

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
adjState Key  (TSym '=')  outer           = (_ ** switch outer)
adjState Value NL         TopLevel        = (Key ** TopLevel)
adjState Value (TSym ']') (InArray outer) = (_ ** outer)
adjState Value (TSym '}') (InTable outer) = (_ ** outer)
adjState Value (TSym '[') outer           = (_ ** InArray outer)
adjState Value (TSym '{') outer           = (Key ** InTable outer)
adjState Value (TSym ',') (InTable outer) = (Key ** InTable outer)
adjState t     _          st              = (t ** st)

-- decides on the lexer to run depending on the current
-- context
%inline
anyTok : Ctxt -> Tok Char TomlToken
anyTok Key   = anyKey
anyTok Value = val

-- We convert a `Space` token to a `NL` if the sequence of
-- spaces contains a line break and we are not in an array
-- literal (where arbitrary line breaks are allowed).
adjSpace : LexState c -> (hasNL : Bool) -> TomlToken -> TomlToken
adjSpace (InArray _) _    t     = t
adjSpace _           True Space = NL
adjSpace _           _    t     = t

--------------------------------------------------------------------------------
--          Post Processing
--------------------------------------------------------------------------------

-- to simplify the parser, we group paths of dot-separated key in
-- a single pass when converting the `SnocList` of tokens to
-- a list of tokens.
groupKeys :
     List (Bounded TomlToken)
  -> Bounded (List String)
  -> SnocList (Bounded TomlToken)
  -> List (Bounded TomlToken)

-- to simplify the parser, we remove non-relevant tokens in
-- a single pass when converting the `SnocList` of tokens to
-- a list of tokens.
postProcess :
     List (Bounded TomlToken)
  -> SnocList (Bounded TomlToken)
  -> List (Bounded TomlToken)

groupKeys ts ks (sx :< B (TKey [s]) bk :< B '.' bd) =
  groupKeys ts (B (s::ks.val) (ks.bounds <+> bd <+> bk)) sx
groupKeys ts ks (sx :< x) = postProcess (x :: map TKey ks :: ts) sx
groupKeys ts ks [<] = map TKey ks :: ts

postProcess ts [<]       = ts
postProcess ts (sx :< x) = case x.val of
  TKey s  => groupKeys ts (x $> s) sx
  Comment => postProcess ts sx
  Space   => postProcess ts sx
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
  -> Either (Bounded StopReason) (List $ Bounded TomlToken)
lex st pos sx []           _      = Right $ postProcess [] sx
lex st pos sx (x :: xs) (SA r) = case anyTok t (x::xs) of
  Succ val ys @{p} =>
    let pos2        := endPos pos p
        v           := adjSpace st (pos2.line > pos.line) val
        (t2 ** st2) := adjState t v st
     in lex st2 pos2 (sx :< bounded v pos pos2) ys r
  Stop start errEnd y => Left $ boundedErr pos start errEnd y

export %inline
lexToml : String -> Either (Bounded StopReason) (List $ Bounded TomlToken)
lexToml s = lex {t = Key} TopLevel begin [<] (unpack s) suffixAcc
