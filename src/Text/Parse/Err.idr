module Text.Parse.Err

import Text.Lex.Tokenizer
import Text.Parse.FC
import Derive.Prelude

%language ElabReflection
%default total

public export
data ParseErr : Type -> Type where
  EOI         : ParseErr e
  ExpectedEOI : ParseErr e
  Custom      : (err : e) -> ParseErr e

%runElab derive "ParseErr" [Show,Eq]

public export
Functor ParseErr where
  map _ EOI         = EOI
  map _ ExpectedEOI = ExpectedEOI
  map f (Custom v)  = Custom (f v)

public export
Foldable ParseErr where
  foldr f acc (Custom v) = f v acc
  foldr f acc _          = acc

  foldl f acc (Custom v) = f acc v
  foldl f acc _          = acc

  foldMap f (Custom v) = f v
  foldMap f _          = neutral

  toList (Custom v) = [v]
  toList _          = []

  null (Custom v) = False
  null _          = True

public export
Traversable ParseErr where
  traverse f EOI         = pure EOI
  traverse f ExpectedEOI = pure ExpectedEOI
  traverse f (Custom v)  = Custom <$> f v

public export
data ReadError : Type -> Type where
  LexFailed   : FileContext -> StopReason -> ReadError e
  ParseFailed : List1 (FileContext, ParseErr e) -> ReadError e
