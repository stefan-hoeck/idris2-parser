module Text.ParseError

import Text.Bounds
import Text.FC
import Derive.Prelude

%default total
%language ElabReflection

--------------------------------------------------------------------------------
--          Lexing Errors
--------------------------------------------------------------------------------

public export
data StopReason : Type where
  InvalidEscape  : StopReason
  InvalidControl : Char -> StopReason
  UnknownToken   : StopReason
  EOI            : StopReason
  ExpectedEOI    : StopReason

export
Interpolation StopReason where
  interpolate InvalidEscape      = "Invalid escape sequence"
  interpolate (InvalidControl c) = "Invalid control character: \{show c}"
  interpolate UnknownToken       = "Unknown token"
  interpolate EOI                = "End of input"
  interpolate ExpectedEOI        = "Expected end of input"

%runElab derive "StopReason" [Show,Eq]

--------------------------------------------------------------------------------
--          Parse Errors
--------------------------------------------------------------------------------

public export
data ParseError : (token, err : Type) -> Type where
  Reason      : StopReason -> ParseError t e
  Expected    : t -> ParseError t e
  Unexpected  : t -> ParseError t e
  Unclosed    : t -> ParseError t e
  Custom      : (err : e) -> ParseError t e

%runElab derive "ParseError" [Show,Eq]

public export
fromVoid : ParseError t Void -> ParseError t e
fromVoid (Reason x)     = Reason x
fromVoid (Expected x)   = Expected x
fromVoid (Unexpected x) = Unexpected x
fromVoid (Unclosed x)   = Unclosed x
fromVoid (Custom err) impossible

export
Interpolation t => Interpolation e => Interpolation (ParseError t e) where
  interpolate (Reason s)     = interpolate s
  interpolate (Expected x)   = "Expected \{x}"
  interpolate (Unexpected x) = "Unexpected \{x}"
  interpolate (Unclosed x)   = "Unclosed \{x}"
  interpolate (Custom err)   = interpolate err

public export
interface FailParse (0 m : Type -> Type) (0 t,e : Type) | m where
  parseFail : Bounds -> ParseError t e -> m a

public export
FailParse (Either $ Bounded $ ParseError t e) t e where
  parseFail b err = Left (B err b)

public export %inline
custom : FailParse m t e => Bounds -> e -> m a
custom b = parseFail b . Custom

public export %inline
expected : FailParse m t e => Bounds -> t -> m a
expected b = parseFail b . Expected

public export %inline
unclosed : FailParse m t e => Bounds -> t -> m a
unclosed b = parseFail b . Unclosed

public export %inline
unexpected : FailParse m t e => Bounded t -> m a
unexpected v = parseFail v.bounds (Unexpected v.val)

public export %inline
eoi : FailParse m t e => m a
eoi = parseFail NoBounds (Reason EOI)

public export %inline
expectedEOI : FailParse m t e => Bounds -> m a
expectedEOI b = parseFail b (Reason ExpectedEOI)

--------------------------------------------------------------------------------
--          Pretty Printing Errors
--------------------------------------------------------------------------------

printPair :
     Interpolation a
  => List String
  -> (FileContext,a)
  -> List String
printPair ls (fc,x) = "Error: \{x}" :: printFC fc ls

export
printVirtual :
     Interpolation a
  => String
  -> Bounded a
  -> String
printVirtual s x = unlines $ printPair (lines s) (fromBounded Virtual x)

export
printParseError :
     Interpolation t
  => Interpolation e
  => String
  -> FileContext
  -> ParseError t e
  -> String
printParseError str fc err =
   unlines $ printPair (lines str) (fc,err)

export
printParseErrors :
     Foldable m
  => Interpolation t
  => Interpolation e
  => String
  -> m (FileContext, ParseError t e)
  -> String
printParseErrors str errs =
  let ls := lines str
   in unlines $ toList errs >>= printPair ls
