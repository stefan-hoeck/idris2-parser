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
data InnerError : (err : Type) -> Type where
  ||| A custom error for the current parsing topic
  Custom         : (err : e) -> InnerError e

  ||| Unexpected end of input
  EOI            : InnerError e

  ||| Expected the given token but got something else.
  Expected       : String -> InnerError e

  ||| Expected the given type of character
  ExpectedChar   : CharClass -> InnerError e

  ||| Got more input that we expected
  ExpectedEOI    : InnerError e

  ||| Got an invalid control character
  InvalidControl : Char -> InnerError e

  ||| Got an invalid character escape sequence
  InvalidEscape  : InnerError e

  ||| Got a (usually numeric) value that was out of bounds
  OutOfBounds    : String -> InnerError e

  ||| An unclosed opening token
  Unclosed       : String -> InnerError e

  ||| Got an unexpected token
  Unexpected     : String -> InnerError e

  ||| Got an unknown or invalid token
  Unknown        : String -> InnerError e

%runElab derive "InnerError" [Show,Eq]

public export
Functor InnerError where
  map f (Custom err)        = Custom $ f err
  map f EOI                 = EOI
  map f (Expected x)        = Expected x
  map f (ExpectedChar x)    = ExpectedChar x
  map f ExpectedEOI         = ExpectedEOI
  map f (InvalidControl c1) = InvalidControl c1
  map f InvalidEscape       = InvalidEscape
  map f (OutOfBounds x)     = OutOfBounds x
  map f (Unclosed x)        = Unclosed x
  map f (Unexpected x)      = Unexpected x
  map f (Unknown x)         = Unknown x

export
Interpolation e => Interpolation (InnerError e) where
  interpolate EOI                = "Unexpected end of input"
  interpolate (Expected x)       = "Expected \{x}"
  interpolate (ExpectedChar x)   = "Expected \{x}"
  interpolate ExpectedEOI        = "Expected end of input"
  interpolate (InvalidControl c) = "Invalid control character: \{show c}"
  interpolate InvalidEscape      = "Invalid escape sequence"
  interpolate (OutOfBounds x)    = "Value out of bounds: \{x}"
  interpolate (Unclosed x)       = "Unclosed \{x}"
  interpolate (Unexpected x)     = "Unexpected \{x}"
  interpolate (Unknown x)        = "Unknown or invalid token: \{x}"
  interpolate (Custom err)       = interpolate err

--------------------------------------------------------------------------------
--          Interface
--------------------------------------------------------------------------------

public export
interface FailParse (0 m : Type -> Type) (0 e : Type) | m where
  parseFail : Bounds -> InnerError e -> m a

public export %inline
FailParse (Either $ Bounded $ InnerError e) e where
  parseFail b err = Left (B err b)

public export %inline
FailParse (Result0 b t ts (Bounded $ InnerError y)) y where
  parseFail b err = Fail0 (B err b)

public export %inline
custom : FailParse m e => Bounds -> e -> m a
custom b = parseFail b . Custom

public export %inline
expected : Interpolation t => FailParse m e => Bounds -> t -> m a
expected b = parseFail b . Expected . interpolate

public export %inline
unclosed : Interpolation t => FailParse m e => Bounds -> t -> m a
unclosed b = parseFail b . Unclosed . interpolate

public export %inline
unexpected : Interpolation t => FailParse m e => Bounded t -> m a
unexpected v = parseFail v.bounds (Unexpected . interpolate $ v.val)

public export %inline
eoi : FailParse m e => m a
eoi = parseFail NoBounds EOI

public export %inline
expectedEOI : FailParse m e => Bounds -> m a
expectedEOI b = parseFail b ExpectedEOI

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
     {auto int : Interpolation t}
  -> (b : Bounds)
  -> (tok : t)
  -> Result0 b1 (Bounded t) ts (Bounded $ InnerError e) a
  -> Result0 b2 (Bounded t) ts (Bounded $ InnerError e) x
failInParen b tok (Fail0 (B EOI _))   = unclosed b tok
failInParen b tok (Fail0 err)         = Fail0 err
failInParen b tok (Succ0 _ [])        = unclosed b tok
failInParen b tok (Succ0 _ (x :: xs)) = unexpected x

||| Catch-all error generator when no other rule applies.
public export
fail :
     {auto int : Interpolation t}
  -> List (Bounded t)
  -> Result0 b (Bounded t) ts (Bounded $ InnerError y) a
fail (x :: xs) = unexpected x
fail []        = eoi

--------------------------------------------------------------------------------
--          Identities
--------------------------------------------------------------------------------

public export
fromVoid : InnerError Void -> InnerError e
fromVoid EOI                = EOI
fromVoid (Expected x)       = Expected x
fromVoid (ExpectedChar x)   = ExpectedChar x
fromVoid ExpectedEOI        = ExpectedEOI
fromVoid (InvalidControl c) = InvalidControl c
fromVoid InvalidEscape      = InvalidEscape
fromVoid (OutOfBounds x)    = OutOfBounds x
fromVoid (Unclosed x)       = Unclosed x
fromVoid (Unexpected x)     = Unexpected x
fromVoid (Unknown x)        = Unknown x

--------------------------------------------------------------------------------
--          ParseError
--------------------------------------------------------------------------------

||| Pairs a parsing error (`InnerError`)
||| with a text's origin, the error's bound, and
||| the text itself.
public export
record ParseError e where
  constructor PE
  origin  : Origin
  bounds  : Bounds
  content : Maybe String
  error   : InnerError e

%runElab derive "ParseError" [Show,Eq]

export
toStreamError : Origin -> Bounded (InnerError e) -> ParseError e
toStreamError o (B err bs) = PE o bs Nothing err

export
toParseError : Origin -> String -> Bounded (InnerError e) -> ParseError e
toParseError o s (B err bs) = PE o bs (Just s) err

export %inline
leftErr :
     Origin
  -> String
  -> Either (Bounded (InnerError e)) a
  -> Either (ParseError e) a
leftErr o = mapFst . toParseError o

public export
result :
     {auto int : Interpolation t}
  -> Origin
  -> String
  -> Result0 b (Bounded t) ts (Bounded $ InnerError e) a
  -> Either (ParseError e) a
result o s (Fail0 err)           = Left $ toParseError o s err
result _ s (Succ0 res [])        = Right res
result o s (Succ0 res (x :: xs)) = leftErr o s $ unexpected x

export
Interpolation e => Interpolation (ParseError e) where
  interpolate (PE origin bounds cont err) =
    let fc := FC origin bounds
     in case cont of
          Just c  => unlines $ "Error: \{err}" :: printFC fc (lines c)
          Nothing => unlines ["Error: \{err}", interpolate fc]
