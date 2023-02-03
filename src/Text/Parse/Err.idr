module Text.Parse.Err

import Data.String
import Derive.Prelude
import Text.Lex
import Text.Parse.FC

%language ElabReflection
%default total

public export
data ParseError : (token, err : Type) -> Type where
  EOI         : ParseError t e
  ExpectedEOI : ParseError t e
  Expected    : t -> ParseError t e
  Unexpected  : t -> ParseError t e
  Custom      : (err : e) -> ParseError t e

%runElab derive "ParseError" [Show,Eq]

export
Interpolation t => Interpolation e => Interpolation (ParseError t e) where
  interpolate EOI            = "End of input"
  interpolate ExpectedEOI    = "Expected end of input"
  interpolate (Expected x)   = "Expected \{x}"
  interpolate (Unexpected x) = "Unexpected \{x}"
  interpolate (Custom err)   = interpolate err

printPair :
     Interpolation a
  => List String
  -> (FileContext,a)
  -> List String
printPair ls (fc,x) = "Error: \{x}" :: printFC fc ls

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
unexpected : FailParse m t e => Bounded t -> m a
unexpected v = parseFail v.bounds (Unexpected v.val)

public export %inline
eoi : FailParse m t e => m a
eoi = parseFail NoBounds EOI

public export %inline
expectedEOI : FailParse m t e => Bounds -> m a
expectedEOI b = parseFail b ExpectedEOI

--------------------------------------------------------------------------------
--          ReadError
--------------------------------------------------------------------------------

public export
data ReadError : Type -> Type -> Type where
  LexFailed   : FileContext -> StopReason -> ReadError t e
  ParseFailed : List1 (FileContext, ParseError t e) -> ReadError t e

%runElab derive "ReadError" [Show,Eq]

public export
parseFailed : Origin -> List1 (Bounded $ ParseError t e) -> ReadError t e
parseFailed o = ParseFailed . map (\b => (FC o b.bounds, b.val))

public export
parseError :
     Origin
  -> Either (Bounded $ ParseError t e) a
  -> Either (ReadError t e) a
parseError o = mapFst (parseFailed o . singleton)

export
printReadError :
     Interpolation t
  => Interpolation e
  => String
  -> ReadError t e
  -> String
printReadError str err =
  let ls := lines str
   in case err of
     LexFailed fc y => unlines $ printPair ls (fc,y)
     ParseFailed ps => unlines $ concatMap (printPair ls) ps
