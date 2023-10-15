module Text.WebIDL.Lexer

import Text.Bounds
import Text.Lex.Manual
import Text.WebIDL.Types

%default total

--------------------------------------------------------------------------------
--          Noise
--------------------------------------------------------------------------------

keep : IdlToken -> Bool
keep Comment = False
keep Space   = False
keep _       = True

spaces : AutoTok e IdlToken
spaces ('\n' :: xs) = spaces xs
spaces ('\r' :: xs) = spaces xs
spaces ('\t' :: xs) = spaces xs
spaces (' ' :: xs)  = spaces xs
spaces xs           = Succ Space xs

comment : AutoTok e IdlToken
comment ('\n' :: xs) = Succ Comment ('\n' :: xs)
comment (x :: xs)    = comment xs
comment []           = Succ Comment []

mlComment : AutoTok e IdlToken
mlComment ('*' :: '/' :: xs) = Succ Comment xs
mlComment (x :: xs)          = mlComment xs
mlComment []                 = eoiAt p

string : SnocList Char -> AutoTok e IdlToken
string sc ('"' :: xs) = Succ (SLit $ MkStrLit $ cast sc) xs
string sc (x :: xs)   = string (sc :< x)  xs
string _  []          = eoiAt p

-- Takes a valid identifier and converts it either
-- to a FloatLit, a Keyword, or an Identifier
toIdent : String -> IdlToken
toIdent "Infinity"  = FLit Infinity
toIdent "-Infinity" = FLit NegativeInfinity
toIdent "NaN"       = FLit NaN
toIdent s           = maybe (Ident $ MkIdent s) Key (refineKeyword s)

ident : SnocList Char -> AutoTok e IdlToken
ident sc ('-' :: xs) = ident (sc :< '-') xs
ident sc ('_' :: xs) = ident (sc :< '_') xs
ident sc (x   :: xs) =
  if isAlphaNum x then ident (sc :< x) xs else Succ (toIdent $ cast sc) (x::xs)
ident sc  []         = Succ (toIdent $ cast sc) []

--------------------------------------------------------------------------------
--          Numbers
--------------------------------------------------------------------------------

toInt : Signum -> Nat -> Integer
toInt Plus  n = cast n
toInt Minus n = negate $ cast n

toNum : Integer -> Maybe Nat -> Maybe Integer -> IdlToken
toNum i Nothing Nothing   = ILit $ I i
toNum i mn      (Just ex) = FLit $ Exp i mn ex
toNum i (Just ad) Nothing = FLit $ NoExp i ad

exp : Integer -> Maybe Nat -> AutoTok e IdlToken
exp i mn (x :: xs) =
  if toLower x == 'e' then toNum i mn . Just <$> intPlus xs
  else Succ (toNum i mn Nothing) (x::xs)
exp i mn []        = Succ (toNum i mn Nothing) []

dot : Integer -> Nat -> AutoTok e IdlToken
dot i n (x :: xs) =
  if isDigit x then dot i (10*n + digit x) xs else exp i (Just n) (x::xs)
dot i n []        = Succ (toNum i (Just n) Nothing) []

rest : Integer -> AutoTok e IdlToken
rest i ('.'::x::xs) = if isDigit x then dot i (digit x) xs else unknownRange p xs
rest i ('.'::[])    = unknown p
rest i xs           = exp i Nothing xs

num : Signum -> Nat -> AutoTok e IdlToken
num s n (x :: xs) =
  if isDigit x then num s (n*10 + digit x) xs else rest (toInt s n) (x::xs)
num s n []        = Succ (ILit $ I $ toInt s n) []

--------------------------------------------------------------------------------
--          Numbers
--------------------------------------------------------------------------------

isFloat : List Char -> Bool
isFloat ('.' :: _) = True
isFloat ('e' :: _) = True
isFloat ('E' :: _) = True
isFloat _          = False

term : Tok e IdlToken
term ('"':: xs) = string [<] xs
term ('/'::'/':: xs) = comment xs
term ('/'::'*':: xs) = mlComment xs
term ('0'::'x':: xs) = ILit . Hex <$> hex xs
term ('0'::'X':: xs) = ILit . Hex <$> hex xs
term ('0'::xs)       =
  if isFloat xs then rest 0 xs else ILit . Oct <$> oct ('0'::xs)
term ('.'::'.'::'.'::xs) = Succ (Other Ellipsis) xs
term ('_':: x::xs)   =
  if isAlpha x then ident [<'_',x] xs
  else Succ (Other $ Symb '_') (x::xs)
term ('-':: x::xs)   =
  if isAlpha x then ident [<'-',x] xs
  else if isDigit x then num Minus (digit x) xs
  else Succ (Other $ Symb '-') (x::xs)
term (x::xs)         =
  if      isAlpha x then ident [<x] xs
  else if isDigit x then num Plus (digit x) xs
  else if isSpace x then spaces xs
  else Succ (Other $ Symb x) xs
term [] = eoiAt Same

public export
0 ParseErr : Type
ParseErr = ParseError IdlToken IdlError

go :
     SnocList (Bounded IdlToken)
 -> (pos   : Position)
 -> (cs    : List Char)
 -> (0 acc : SuffixAcc cs)
 -> Either (Bounded ParseErr) (List (Bounded IdlToken))
go sx _ []    _     = Right (sx <>> [])
go sx pos xs (SA r) = case term xs of
  Succ t xs' @{prf@(Uncons _)} =>
    let pos2 := endPos pos prf
        sx'  := if keep t then (sx :< bounded t pos pos2) else sx
     in go sx' pos2 xs' r
  Succ _ _ => Left $ oneChar NoConsumption pos
  Fail start errEnd r => Left $ boundedErr pos start errEnd (voidLeft r)

||| Generates a list of IdlTokens
||| from an input string, removing unnecessary tokens by
||| means of `isNoise`.
export %inline
lexIdl : String -> Either (Bounded ParseErr) (List $ Bounded IdlToken)
lexIdl s = go [<] begin (unpack s) suffixAcc
