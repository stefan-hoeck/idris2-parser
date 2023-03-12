module Text.ParseError

import Data.List.Suffix.Result0
import Derive.Prelude
import Text.Bounds
import Text.FC

%default total
%language ElabReflection

public export
data DigitType : Type where
  Bin : DigitType
  Oct : DigitType
  Dec : DigitType
  Hex : DigitType

%runElab derive "DigitType" [Show,Eq,Ord]

export
Interpolation DigitType where
  interpolate Bin = "a binary digit ('0' or '1')"
  interpolate Oct = "an octal digit ('0' to '7')"
  interpolate Dec = "a decimal digit ('0' to '9')"
  interpolate Hex = "a hexadecimal digit ('0' to '9' or 'a' to 'f')"

public export
data CharClass : Type where
  ||| A whitespace character
  Space : CharClass

  ||| A digit
  Digit : DigitType -> CharClass

  ||| An upper-case letter
  Upper : CharClass

  ||| A lower-case letter
  Lower : CharClass

  ||| An upper- or lower-case letter
  Alpha : CharClass

  ||| An upper- or lower-case letter or a decimal digit
  AlphaNum : CharClass

%runElab derive "CharClass" [Show,Eq,Ord]

export
Interpolation CharClass where
  interpolate Space     = "a space character"
  interpolate (Digit x) = interpolate x
  interpolate Upper     = "an upper-case letter"
  interpolate Lower     = "a lower-case letter"
  interpolate Alpha     = "a letter ('a' to 'z' or 'A' to 'Z')"
  interpolate AlphaNum  = "a letter or a digit"

--------------------------------------------------------------------------------
--          Parse Errors
--------------------------------------------------------------------------------

public export
data ParseError : (token, err : Type) -> Type where
  ||| A custom error for the current parsing topic
  Custom         : (err : e) -> ParseError t e

  ||| Unexpected end of input
  EOI            : ParseError t e

  ||| Expected the given token but got something else.
  Expected       : Either String t -> ParseError t e

  ||| Expected the given type of character
  ExpectedChar   : CharClass -> ParseError t e

  ||| Got more input that we expected
  ExpectedEOI    : ParseError t e

  ||| Got an invalid control character
  InvalidControl : Char -> ParseError t e

  ||| Got an invalid character escape sequence
  InvalidEscape  : ParseError t e

  ||| Got a (usually numeric) value that was out of bounds
  OutOfBounds    : Either String t -> ParseError t e

  ||| An unclosed opening token
  Unclosed       : Either String t -> ParseError t e

  ||| Got an unexpected token
  Unexpected     : Either String t -> ParseError t e

  ||| Got an unknown or invalid token
  Unknown        : Either String t -> ParseError t e

%runElab derive "ParseError" [Show,Eq]

public export
Bifunctor ParseError where
  bimap f g (Custom err)        = Custom $ g err
  bimap f g EOI                 = EOI
  bimap f g (Expected x)        = Expected $ map f x
  bimap f g (ExpectedChar x)    = ExpectedChar x
  bimap f g ExpectedEOI         = ExpectedEOI
  bimap f g (InvalidControl c1) = InvalidControl c1
  bimap f g InvalidEscape       = InvalidEscape
  bimap f g (OutOfBounds x)     = OutOfBounds $ map f x
  bimap f g (Unclosed x)        = Unclosed $ map f x
  bimap f g (Unexpected x)      = Unexpected $ map f x
  bimap f g (Unknown x)         = Unknown $ map f x

%inline
interpEither : Interpolation t => Either String t -> String
interpEither = either id interpolate

export
Interpolation t => Interpolation e => Interpolation (ParseError t e) where
  interpolate EOI                = "Unexpected end of input"
  interpolate (Expected x)       = "Expected \{interpEither x}"
  interpolate (ExpectedChar x)   = "Expected \{x}"
  interpolate ExpectedEOI        = "Expected end of input"
  interpolate (InvalidControl c) = "Invalid control character: \{show c}"
  interpolate InvalidEscape      = "Invalid escape sequence"
  interpolate (OutOfBounds x)    = "Value out of bounds: \{interpEither x}"
  interpolate (Unclosed x)       = "Unclosed \{interpEither x}"
  interpolate (Unexpected x)     = "Unexpected \{interpEither x}"
  interpolate (Unknown x)        = "Unknown or invalid token: \{interpEither x}"
  interpolate (Custom err)       = interpolate err

--------------------------------------------------------------------------------
--          Interface
--------------------------------------------------------------------------------

public export
interface FailParse (0 m : Type -> Type) (0 t,e : Type) | m where
  parseFail : Bounds -> ParseError t e -> m a

public export %inline
FailParse (Either $ Bounded $ ParseError t e) t e where
  parseFail b err = Left (B err b)

public export %inline
FailParse (Result0 b t ts (Bounded $ ParseError x y)) x y where
  parseFail b err = Fail0 (B err b)

public export %inline
custom : FailParse m t e => Bounds -> e -> m a
custom b = parseFail b . Custom

public export %inline
expected : FailParse m t e => Bounds -> t -> m a
expected b = parseFail b . Expected . Right

public export %inline
unclosed : FailParse m t e => Bounds -> t -> m a
unclosed b = parseFail b . Unclosed . Right

public export %inline
unexpected : FailParse m t e => Bounded t -> m a
unexpected v = parseFail v.bounds (Unexpected . Right $ v.val)

public export %inline
eoi : FailParse m t e => m a
eoi = parseFail NoBounds EOI

public export %inline
expectedEOI : FailParse m t e => Bounds -> m a
expectedEOI b = parseFail b ExpectedEOI

--------------------------------------------------------------------------------
--          Pretty Printing Errors
--------------------------------------------------------------------------------

printPair : Interpolation a => List String -> (FileContext,a) -> List String
printPair ls (fc,x) = "Error: \{x}" :: printFC fc ls

export
printVirtual : Interpolation a => String -> Bounded a -> String
printVirtual s x = unlines $ printPair (lines s) (fromBounded Virtual x)

export
printParseError : Interpolation a => String -> FileContext -> a -> String
printParseError str fc err =
   unlines $ printPair (lines str) (fc,err)

export
printParseErrors :
     Foldable m
  => Interpolation a
  => String
  -> m (FileContext, a)
  -> String
printParseErrors str errs =
  let ls := lines str
   in unlines $ toList errs >>= printPair ls

--------------------------------------------------------------------------------
--          Parser Errors
--------------------------------------------------------------------------------

||| General catch-all error generator when parsing within some kind
||| of opening token: Will fail with an `Unclosed` error if at the
||| end of input, or with an `Unknown` error wrapping the next token.
||| Otherwise, will rethrow the current error.
|||
||| @ b   : Bounds of the opening paren or token
||| @ tok : Opening paren or token
||| @ res : Current parsing result
public export
failInParen :
     (b : Bounds)
  -> (tok : t)
  -> Result0 b1 (Bounded t) ts (Bounded $ ParseError t y) a
  -> Result0 b2 (Bounded t) ts (Bounded $ ParseError t y) x
failInParen b tok (Fail0 (B EOI _))   = unclosed b tok
failInParen b tok (Fail0 err)         = Fail0 err
failInParen b tok (Succ0 _ [])        = unclosed b tok
failInParen b tok (Succ0 _ (x :: xs)) = unexpected x

||| Like `failInParen`, but with the ability to specify custom
||| "end-of-input" tokens.
|||
||| @ b   : Bounds of the opening paren or token
||| @ tok : Opening paren or token
||| @ eoi : Returns `True` if the given token signals the end of input
||| @ res : Current parsing result
public export
failInParenEOI :
     (b : Bounds)
  -> (tok : t)
  -> (eoi : t -> Bool)
  -> Result0 b1 (Bounded t) ts (Bounded $ ParseError t y) a
  -> Result0 b2 (Bounded t) ts (Bounded $ ParseError t y) x
failInParenEOI b tok f res@(Fail0 (B (Unexpected $ Right t) bs)) =
  if f t then unclosed b tok else failInParen b tok res
failInParenEOI b tok f res@(Succ0 _ (B t _ :: xs)) =
  if f t then unclosed b tok else failInParen b tok res
failInParenEOI b tok f res = failInParen b tok res

||| Catch-all error generator when no other rule applies.
public export
fail : List (Bounded t) -> Result0 b (Bounded t) ts (Bounded $ ParseError t y) a
fail (x :: xs) = unexpected x
fail []        = eoi

public export
result :
     Origin
  -> Result0 b (Bounded t) ts (Bounded $ ParseError t e) a
  -> Either (FileContext, ParseError t e) a
result o (Fail0 err)           = Left $ fromBounded o err
result _ (Succ0 res [])        = Right res
result o (Succ0 res (x :: xs)) = Left $ fromBounded o (Unexpected . Right <$> x)

--------------------------------------------------------------------------------
--          Identities
--------------------------------------------------------------------------------

public export
left : Either e Void -> Either e a
left (Left x) = Left x

public export
voidLeft : ParseError Void e -> ParseError t e
voidLeft EOI                = EOI
voidLeft (Expected x)       = Expected $ left x
voidLeft (ExpectedChar x)   = ExpectedChar x
voidLeft ExpectedEOI        = ExpectedEOI
voidLeft (InvalidControl c) = InvalidControl c
voidLeft InvalidEscape      = InvalidEscape
voidLeft (OutOfBounds x)    = OutOfBounds $ left x
voidLeft (Unclosed x)       = Unclosed $ left x
voidLeft (Unexpected x)     = Unexpected $ left x
voidLeft (Unknown x)        = Unknown $ left x
voidLeft (Custom x)         = Custom x

public export
fromVoid : ParseError Void Void -> ParseError t e
fromVoid EOI                = EOI
fromVoid (Expected x)       = Expected $ left x
fromVoid (ExpectedChar x)   = ExpectedChar x
fromVoid ExpectedEOI        = ExpectedEOI
fromVoid (InvalidControl c) = InvalidControl c
fromVoid InvalidEscape      = InvalidEscape
fromVoid (OutOfBounds x)    = OutOfBounds $ left x
fromVoid (Unclosed x)       = Unclosed $ left x
fromVoid (Unexpected x)     = Unexpected $ left x
fromVoid (Unknown x)        = Unknown $ left x
