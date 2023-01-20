module Text.Parse.Err

import Text.Lex
import Text.Parse.FC
import Derive.Prelude

%language ElabReflection
%default total

public export
data ParseErr : (token, err : Type) -> Type where
  EOI         : ParseErr t e
  ExpectedEOI : ParseErr t e
  Expected    : t -> ParseErr t e
  Unexpected  : t -> ParseErr t e
  Custom      : (err : e) -> ParseErr t e

%runElab derive "ParseErr" [Show,Eq]

public export
data ReadError : Type -> Type -> Type where
  LexFailed   : FileContext -> StopReason -> ReadError t e
  ParseFailed : List1 (FileContext, ParseErr t e) -> ReadError t e

%runElab derive "ReadError" [Show,Eq]

public export
parseFailed : Origin -> List1 (Bounded $ ParseErr t e) -> ReadError t e
parseFailed o = ParseFailed . map (\b => (FC o b.bounds, b.val))
