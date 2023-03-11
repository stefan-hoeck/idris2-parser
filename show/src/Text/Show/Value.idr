module Text.Show.Value

import Data.List1
import Data.Vect
import Derive.Prelude
import Text.Parse.Manual
import Text.PrettyPrint.Bernardy

%language ElabReflection

%default total

||| A name.
public export
record VName where
  constructor MkName
  unName : String

public export %inline
Cast (SnocList Char) VName where
  cast = MkName . cast

%runElab derive "VName" [Show,Eq,Ord,FromString,Semigroup,Monoid]

public export
Interpolation VName where interpolate (MkName n) = n

public export
Pretty VName where
  prettyPrec _ = line . unName

||| Generic Idris values.
||| The `String` in the literals is the text for the literals "as is".
|||
||| A chain of infix constructors means that they appeared in the input string
||| without parentheses, i.e
|||
||| `1 :+: 2 :*: 3` is represented with `InfixCons 1 [(":+:",2),(":*:",3)]`, whereas
|||
||| `1 :+: (2 :*: 3)` is represented with `InfixCons 1 [(":+:",InfixCons 2 [(":*:",3)])]`.
public export
data Value = Con VName (List Value)
           | InfixCons Value (List (VName,Value))
           | Rec VName (List (VName,Value))
           | Tuple Value Value (List Value) -- At least two values
           | Lst (List Value)
           | Neg Value
           | Natural String
           | Dbl String
           | Chr String
           | Str String

%runElab derive "Value" [Show, Eq]

||| Displays an applied binary operator.
||| If the same operator appears several times in a row,
||| this is treated as a list of infix constructors.
public export
binOp : VName -> Value -> Value -> Value
binOp op pvx pvy =
   case pvy of
        InfixCons pv1 pairs@((op2, pv2) :: xs) =>
          if op2 == op then InfixCons pvx ((op,pvy) :: pairs)
                       else InfixCons pvx [(op,pvy)]
        _ => InfixCons pvx [(op,pvy)]

hidden : (Bool,Value)
hidden = (True, Con "_" [])

toVal : Bool -> Lazy Value -> (Bool,Value)
toVal True  _ = hidden
toVal False v = (False, v)

0 V,VN : Type
V  = Value
VN = VName

parameters (collapse : Bool) (hide : VName -> Bool)

  -- the `Bool` flag is set to `True`, if the wrapped value
  -- was hidden and corresponds to `Con "_" []`.
  val : V -> (Bool,V)

  ops : Bool -> SnocList (VN,V) -> V -> List (VN,V) -> (Bool,V)
  ops h sv v0 []            = toVal h $ InfixCons v0 (sv <>> [])
  ops h sv v0 ((n,v) :: vs) =
    let (h2,w) := val v in ops (h && h2) (sv :< (n,w)) v0 vs

  hrec : Bool -> SnocList (VN,V) -> VN -> List (VN,V) -> (Bool,V)
  hrec h sv nm [] = toVal h $ Rec nm (sv <>> [])
  hrec h sv nm ((n,v) :: vs) = case val v of
    (False, w) => hrec False (sv :< (n,w)) nm vs
    (True,_)   => hrec h sv n vs

  hcon : Bool -> SnocList V -> VN -> List V -> (Bool,V)
  hcon h sv n [] = toVal h $ Con n (sv <>> [])
  hcon h sv n (v :: vs) = let (h2,w) := val v in hcon (h && h2) (sv :< w) n vs

  lst : Bool -> SnocList V -> List V -> (Bool,V)
  lst h sv [] = toVal h $ Lst (sv <>> [])
  lst h sv (v :: vs) = let (h2,w) := val v in lst (h && h2) (sv :< w) vs

  val (Con x xs) =
    if hide x then hidden else hcon (isCons xs && collapse) [<] x xs

  val (InfixCons v ps) =
    if any (hide . fst) ps then hidden
    else let (b,w) := val v in ops (b && collapse) [<] w ps

  val (Rec x xs) =
    if hide x then hidden else hrec (isCons xs && collapse) [<] x xs

  val (Lst xs) = lst (isCons xs && collapse) [<] xs

  val (Neg v) = let (b,w) := val v in (b,w)

  val (Tuple v1 v2 vs) =
    let (b1,w1)     := val v1
        (b2,w2)     := val v2
        (b3,Lst ws) := lst (b1 && b2 && collapse) [<] vs | _ => hidden
     in toVal b3 $ Tuple w1 w2 ws

  val (Natural x) = (False,Natural x)
  val (Dbl x)     = (False,Dbl x)
  val (Chr x)     = (False,Chr x)
  val (Str x)     = (False,Str x)

  ||| Hide constructors matching the given predicate.
  ||| If the hidden value is in a record, we also hide
  ||| the corresponding record field.
  |||
  ||| If the boolean flag is true, then we also hide
  ||| constructors all of whose fields were hidden.
  export
  hideCon : Value -> Value
  hideCon = snd . val

--------------------------------------------------------------------------------
--          Tokenizer
--------------------------------------------------------------------------------

public export
data Token : Type where
  Lit    : Value -> Token
  Id     : VName -> Token
  Op     : VName -> Token
  Symbol : Char -> Token
  EOI    : Token

%runElab derive "Token" [Show,Eq]

export
Interpolation Token where
  interpolate (Lit x)    = case x of
    Con y []    => interpolate y
    Rec y []    => interpolate y
    Lst []      => "[]"
    Natural str => str
    Dbl str     => str
    Chr str     => str
    Str str     => str
    x           => show x
  interpolate (Id str)   = interpolate str
  interpolate (Op str)   = interpolate str
  interpolate (Symbol c) = show c
  interpolate EOI        = "end of input"

public export
data Err : Type where
  ExpectedId : Err

%runElab derive "Err" [Show,Eq]

export
Interpolation Err where
  interpolate ExpectedId = "Expected an identifier"

public export
0 PSErr : Type
PSErr = ParseError Token Err

public export %inline
fromChar : Char -> Token
fromChar = Symbol

isIdentStart : Char -> Bool
isIdentStart '_' = True
isIdentStart  x  = isAlpha x

isIdentTrailing : Char -> Bool
isIdentTrailing '\'' = True
isIdentTrailing '_'  = True
isIdentTrailing x    = isAlphaNum x || x > chr 160

ident : AutoShift False
ident ('.'::x::t) = if isIdentStart x then ident t else Succ ('.'::x::t)
ident (x :: t)    = if isIdentTrailing x then ident t else Succ (x::t)
ident []          = Succ []

opChars : List Char
opChars = unpack ":!#$%&*+./<=>?@\\^|-~"

%inline isOp : Char -> Bool
isOp c = c `elem` opChars

toOp : SnocList Char -> Token
toOp [<'='] = '='
toOp sc     = Op $ cast sc

sfx :
     (SnocList Char -> Token)
  -> ShiftRes True [<] ts
  -> LexRes True ts e Token
sfx = suffix

%inline nat,dbl :
     ShiftRes  True [<] ts
  -> LexRes True ts e Token
nat = suffix (Lit . Natural . cast)

dbl = suffix $ \sc =>
  if all isDigit sc then Lit (Natural $ cast sc) else Lit (Dbl $ cast sc)

strLit : AutoShift True
strLit ('\\' :: x :: xs) = strLit {b} xs
strLit ('"' :: xs)       = Succ xs
strLit (x :: xs)         = strLit {b} xs
strLit []                = eoiAt sh

charLit : AutoShift True
charLit ('\\' :: x :: xs) = charLit {b} xs
charLit ('\'' :: xs)      = Succ xs
charLit (x :: xs)         = charLit {b} xs
charLit []                = eoiAt sh

tok : Tok True e Token
tok ('0' :: 'x' :: t) = nat $ takeWhile1 {b = True} isHexDigit t
tok ('0' :: 'X' :: t) = nat $ takeWhile1 {b = True} isHexDigit t
tok ('0' :: 'o' :: t) = nat $ takeWhile1 {b = True} isOctDigit t
tok ('0' :: 'b' :: t) = nat $ takeWhile1 {b = True} isBinDigit t
tok ('(' :: t)  = Succ '(' t
tok (')' :: t)  = Succ ')' t
tok ('{' :: t)  = Succ '{' t
tok ('}' :: t)  = Succ '}' t
tok ('[' :: t)  = Succ '[' t
tok (']' :: t)  = Succ ']' t
tok (',' :: t)  = Succ ',' t
tok ('\'' :: t) = sfx (Lit . Chr . cast) $ charLit {b = True} t
tok ('"'  :: t) = sfx (Lit . Str . cast) $ strLit {b = True} t
tok (x :: t)  =
  if      isOp x then sfx toOp $ takeWhile isOp t
  else if isDigit x then dbl $ number [<] (x::t)
  else if isIdentStart x then sfx (Id . cast) $ ident t
  else unknown Same
tok []         = eoiAt Same

post :
     List (Bounded Token)
  -> SnocList (Bounded Token)
  -> List (Bounded Token)
post xs (sx :< B '(' c :< B (Op s) d :< B ')' e) = case sx of
  sy :< B (Id n) a :< B (Op ".") b =>
    post (B (Id $ MkName "\{n}.(\{s})") (a <+> b <+> c <+> d <+> e) :: xs) sy
  _ => post (B (Id $ MkName "(\{s})") (c <+> d <+> e) :: xs) sx
post xs (sx :< x) = post (x :: xs) sx
post xs [<]       = xs

go :
     SnocList (Bounded Token)
 -> (pos   : Position)
 -> (cs    : List Char)
 -> (0 acc : SuffixAcc cs)
 -> Either (Bounded PSErr) (List (Bounded Token))
go sx pos ('\n' :: xs) (SA r) = go sx (incLine pos) xs r
go sx pos (x :: xs)    (SA r) =
  if isSpace x
     then go sx (incCol pos) xs r
     else case tok (x::xs) of
       Succ t xs' @{prf} =>
         let pos2 := addCol (toNat prf) pos
          in go (sx :< bounded t pos pos2) pos2 xs' r
       Fail start errEnd r => Left $ boundedErr pos start errEnd (voidLeft r)
go sx pos [] _ = Right (post [B EOI $ oneChar pos] sx)

export
tokens : String -> Either (Bounded PSErr) (List (Bounded Token))
tokens s = go [<] begin (unpack s) suffixAcc

--------------------------------------------------------------------------------
--          Parser
--------------------------------------------------------------------------------

toInfx : List (VName,Value) -> SnocList (VName,Value) -> Value -> Value
toInfx xs (sx :< (n,v')) v = toInfx ((n,v) :: xs) sx v'
toInfx [] [<] v = v
toInfx ps [<] v = InfixCons v ps

toTpl : List Value -> Value
toTpl [] = Con "()" []
toTpl (x :: []) = x
toTpl (x :: (y :: xs)) = Tuple x y xs

0 Rule : Bool -> Type -> Type
Rule b t =
     (xs : List $ Bounded Token)
  -> (0 acc : SuffixAcc xs)
  -> Res b Token xs Err t

list : Bounds -> SnocList Value -> Rule True Value

tpl : Bounds -> SnocList Value -> Rule True Value

rec : VName -> Bounds -> SnocList (VName,Value) -> Rule True Value

infx : SnocList (VName,Value) -> Rule True Value

args : VName -> SnocList Value -> Rule False Value

value,single,applied : Rule True Value

applied (B (Lit y) _ :: xs) _        = Succ0 y xs
applied (B (Id y) _ :: xs) _         = Succ0 (Con y []) xs
applied (B '[' _ :: B ']' _ :: xs) _ = Succ0 (Lst []) xs
applied (B '[' b :: xs) (SA r)       = succT $ list b [<] xs r
applied (B '(' _ :: B ')' _ :: xs) _ = Succ0 (Con "()" []) xs
applied (B '(' b :: xs) (SA r)       = succT $ tpl b [<] xs r
applied (x::xs) _                    = unexpected x
applied [] _                         = eoi

single (B (Op "-") _ :: xs) (SA r)                = succT $ map Neg (applied xs r)
single (B (Id y) _ :: B '{' _ :: B '}' _ :: xs) _ = Succ0 (Rec y []) xs
single (B (Id y) _ :: B '{' b :: xs) (SA r)       = succT $ rec y b [<] xs r
single (B (Id y) _ :: xs) (SA r)                  = succT $ args y [<] xs r
single xs sa                                      = applied xs sa

value xs sa = infx [<] xs sa

args n sv xs sa@(SA r) = case applied xs sa of
  Succ0 v xs' => succF $ args n (sv :< v) xs' r
  Fail0 _     => Succ0 (Con n $ sv <>> []) xs

list b sv xs sa@(SA r) = case value xs sa of
  Succ0 v (B ',' _ :: ys)  => succT $ list b (sv :< v) ys r
  Succ0 v (B ']' _ :: ys)  => Succ0 (Lst $ sv <>> [v]) ys
  res                      => failInParen b '[' res

tpl b sv xs sa@(SA r) = case value xs sa of
  Succ0 v (B ',' _ :: ys)  => succT $ tpl b (sv :< v) ys r
  Succ0 v (B ')' _ :: ys)  => Succ0 (toTpl $ sv <>> [v]) ys
  res                      => failInParen b '(' res

infx sv xs sa@(SA r) = case single xs sa of
  Succ0 v (B (Op n) _ :: ys) => succT $ infx (sv :< (n,v)) ys r
  Succ0 v ys                 => Succ0 (toInfx [] sv v) ys
  Fail0 err                  => Fail0 err

rec n b sv (B (Id y) _ :: B '=' _ :: xs) (SA r) = case succT $ value xs r of
  Succ0 v (B ',' _ :: ys) => succT $ rec n b (sv :< (y,v)) ys r
  Succ0 v (B '}' _ :: ys) => Succ0 (Rec n $ sv <>> [(y,v)]) ys
  res                     => failInParen b '{' res
rec _ _ _ (B (Id _) _ ::x::xs) _ = expected x.bounds '='
rec _ _ _ (x::xs) _ = custom x.bounds ExpectedId
rec _ _ _ [] _ = eoi

export
parseValueE : String -> Either (FileContext,PSErr) Value
parseValueE str = case tokens str of
  Left x   => Left $ fromBounded Virtual x
  Right ts => case value ts suffixAcc of
    Fail0 err           => Left $ fromBounded Virtual err
    Succ0 res []        => Right res
    Succ0 res [B EOI _] => Right res
    Succ0 res (x :: xs) => Left (fromBounded Virtual $ Unexpected . Right <$> x)

export
parseValue : String -> Maybe Value
parseValue = either (const Nothing) Just . parseValueE
