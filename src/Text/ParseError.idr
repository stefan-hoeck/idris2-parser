module Text.ParseError

import Data.List.Suffix.Result0
import Derive.Prelude
import Text.Bounds
import Text.FC

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
  interpolate UnknownToken       = "Unknown or invalid token"
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
failInParen b tok (Fail0 (B (Reason EOI) _)) = unclosed b tok
failInParen b tok (Fail0 err)                = Fail0 err
failInParen b tok (Succ0 _ [])               = unclosed b tok
failInParen b tok (Succ0 _ (x :: xs))        = unexpected x

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
result o (Succ0 res (x :: xs)) = Left $ fromBounded o (Unexpected <$> x)
