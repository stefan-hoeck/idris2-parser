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
data InnerError : (token, err : Type) -> Type where
  ||| A custom error for the current parsing topic
  Custom         : (err : e) -> InnerError t e

  ||| Unexpected end of input
  EOI            : InnerError t e

  ||| Expected the given token but got something else.
  Expected       : Either String t -> InnerError t e

  ||| Expected the given type of character
  ExpectedChar   : CharClass -> InnerError t e

  ||| Got more input that we expected
  ExpectedEOI    : InnerError t e

  ||| Got an invalid control character
  InvalidControl : Char -> InnerError t e

  ||| Got an invalid character escape sequence
  InvalidEscape  : InnerError t e

  ||| Got a (usually numeric) value that was out of bounds
  OutOfBounds    : Either String t -> InnerError t e

  ||| An unclosed opening token
  Unclosed       : Either String t -> InnerError t e

  ||| Got an unexpected token
  Unexpected     : Either String t -> InnerError t e

  ||| Got an unknown or invalid token
  Unknown        : Either String t -> InnerError t e

%runElab derive "InnerError" [Show,Eq]

public export
Bifunctor InnerError where
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
Interpolation t => Interpolation e => Interpolation (InnerError t e) where
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
  parseFail : Bounds -> InnerError t e -> m a

public export %inline
FailParse (Either $ Bounded $ InnerError t e) t e where
  parseFail b err = Left (B err b)

public export %inline
FailParse (Result0 b t ts (Bounded $ InnerError x y)) x y where
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
  -> Result0 b1 (Bounded t) ts (Bounded $ InnerError t y) a
  -> Result0 b2 (Bounded t) ts (Bounded $ InnerError t y) x
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
  -> Result0 b1 (Bounded t) ts (Bounded $ InnerError t y) a
  -> Result0 b2 (Bounded t) ts (Bounded $ InnerError t y) x
failInParenEOI b tok f res@(Fail0 (B (Unexpected $ Right t) bs)) =
  if f t then unclosed b tok else failInParen b tok res
failInParenEOI b tok f res@(Succ0 _ (B t _ :: xs)) =
  if f t then unclosed b tok else failInParen b tok res
failInParenEOI b tok f res = failInParen b tok res

||| Catch-all error generator when no other rule applies.
public export
fail : List (Bounded t) -> Result0 b (Bounded t) ts (Bounded $ InnerError t y) a
fail (x :: xs) = unexpected x
fail []        = eoi

--------------------------------------------------------------------------------
--          Identities
--------------------------------------------------------------------------------

public export
left : Either e Void -> Either e a
left (Left x) = Left x

public export
voidLeft : InnerError Void e -> InnerError t e
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
fromVoid : InnerError Void Void -> InnerError t e
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

--------------------------------------------------------------------------------
--          ParseError
--------------------------------------------------------------------------------

||| Pairs a parsing error (`InnerError`)
||| with a text's origin, the error's bound, and
||| the text itself.
public export
record ParseError t e where
  constructor PE
  origin  : Origin
  bounds  : Bounds
  content : Maybe String
  error   : InnerError t e

%runElab derive "ParseError" [Show,Eq]

export
toStreamError : Origin -> Bounded (InnerError t e) -> ParseError t e
toStreamError o (B err bs) = PE o bs Nothing err

export
toParseError : Origin -> String -> Bounded (InnerError t e) -> ParseError t e
toParseError o s (B err bs) = PE o bs (Just s) err

public export
result :
     Origin
  -> String
  -> Result0 b (Bounded t) ts (Bounded $ InnerError t e) a
  -> Either (ParseError t e) a
result o s (Fail0 err)           = Left $ toParseError o s err
result _ s (Succ0 res [])        = Right res
result o s (Succ0 res (x :: xs)) =
  Left $ toParseError o s (Unexpected . Right <$> x)

export
Interpolation e => Interpolation t => Interpolation (ParseError t e) where
  interpolate (PE origin bounds cont err) =
    let fc := FC origin bounds
     in case cont of
          Just c  => unlines $ "Error: \{err}" :: printFC fc (lines c)
          Nothing => unlines ["Error: \{err}", interpolate fc]
