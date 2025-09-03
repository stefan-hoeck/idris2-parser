module Text.TSV.Decoder

import Data.List
import Data.List.Quantifiers as LQ
import Data.String
import Data.Vect
import Data.Vect.Quantifiers as VQ
import Text.Lex.Manual.Syntax
import Text.Parse.Manual

%default total

--------------------------------------------------------------------------------
--          CSV Decoders
--------------------------------------------------------------------------------

public export
interface TSVDecoder a where
  constructor MkTSVDecoder
  decodeFrom : Tok False e a

str' : SnocList Char -> AutoTok e String
str' sc [] = Succ (pack $ sc <>> []) []
str' sc (x :: xs) =
  if isControl x then Succ (pack $ sc <>> []) (x::xs) else str' (sc :< x) xs

export
str : Tok False e String
str []      = Succ "" []
str (x::xs) = if isControl x then Succ "" (x::xs) else weaken $ str' [<x] xs

export
refine : Tok b1 e a -> (a -> Maybe b) -> Tok False e b
refine f g cs = case weaken (f cs) of
  Succ va cs2 => case g va of
    Just vb => Succ vb cs2
    Nothing => unknownRange Same cs2
  Fail x y z => Fail x y z

export
refineNum : Tok b1 e a -> (a -> Maybe b) -> Tok False e b
refineNum f g cs = case weaken (f cs) of
  Succ va cs2 @{p} => case g va of
    Just vb => Succ vb cs2
    Nothing => range (OutOfBounds $ packPrefix p) Same cs2
  Fail x y z => Fail x y z

export %inline
natural : (Nat -> Maybe a) -> Tok False e a
natural = refineNum (tok dec)

export %inline
boundedNat : Cast Nat a => Nat -> Tok False e a
boundedNat m = natural $ \x => if x <= m then Just (cast x) else Nothing

export %inline
integral : (Integer -> Maybe a) -> Tok False e a
integral = refineNum (tok int)

export %inline
boundedInt : Cast Integer a => Integer -> Integer -> Tok False e a
boundedInt l u = integral $ \x =>
  if x >= l && x <= u then Just (cast x) else Nothing

export %inline
float : (Double -> Maybe a) -> Tok False e a
float = refineNum double

export %inline
TSVDecoder Bits8 where
  decodeFrom = boundedNat 0xff

export %inline
TSVDecoder Bits16 where
  decodeFrom = boundedNat 0xffff

export %inline
TSVDecoder Bits32 where
  decodeFrom = boundedNat 0xffff_ffff

export %inline
TSVDecoder Bits64 where
  decodeFrom = boundedNat 0xffff_ffff_ffff_ffff

export %inline
TSVDecoder Int8 where
  decodeFrom = boundedInt (-0x80) 0x7f

export %inline
TSVDecoder Int16 where
  decodeFrom = boundedInt (-0x8000) 0x7fff

export %inline
TSVDecoder Int32 where
  decodeFrom = boundedInt (-0x8000_0000) 0x7fff_ffff

export %inline
TSVDecoder Int64 where
  decodeFrom = boundedInt (-0x8000_0000_0000_0000) 0x7fff_ffff_ffff_ffff

export %inline
TSVDecoder Nat where
  decodeFrom cs = weaken $ dec cs

export %inline
TSVDecoder Integer where
  decodeFrom cs = weaken $ int cs

export %inline
TSVDecoder Double where
  decodeFrom cs = weaken $ double cs

export %inline
TSVDecoder String where
  decodeFrom = str

export
TSVDecoder Bool where
  decodeFrom = refine str $ \case
    "True"  => Just True
    "False" => Just False
    "true"  => Just True
    "false" => Just False
    _       => Nothing

--------------------------------------------------------------------------------
--          Derived Decoders
--------------------------------------------------------------------------------

export
TSVDecoder a => TSVDecoder (Maybe a) where
  decodeFrom [] = Succ Nothing []
  decodeFrom (x :: xs) =
    if isControl x then Succ Nothing (x::xs)
    else Just <$> decodeFrom (x::xs)

export
TSVDecoder a => TSVDecoder b => TSVDecoder (a,b) where
  decodeFrom = Tok.[| MkPair decodeFrom decodeFrom |]

--------------------------------------------------------------------------------
--          HList and HVect
--------------------------------------------------------------------------------

export
tab : Tok False e ()
tab ('\t' :: xs) = Succ () xs
tab (x :: xs)    = single (Expected "<tab>") Same
tab []           = eoiAt Same

decAll : All (TSVDecoder . f) ks => Tok False e (LQ.All.All f ks)
decAll @{[]}   = pure []
decAll @{[_]}  = \cs => (::[]) <$> decodeFrom cs
decAll @{_::_} = Tok.do
  v  <- decodeFrom
  tab
  vs <- decAll
  pure $ v :: vs

decAllV : All (TSVDecoder . f) ks => Tok False e (VQ.All.All f ks)
decAllV @{[]}   = pure []
decAllV @{[_]}  = \cs => (::[]) <$> decodeFrom cs
decAllV @{_::_} = Tok.do
  v  <- decodeFrom
  tab
  vs <- decAllV
  pure $ v :: vs

export %inline
All (TSVDecoder . f) ks => TSVDecoder (LQ.All.All f ks) where
  decodeFrom = decAll

export %inline
All (TSVDecoder . f) ks => TSVDecoder (VQ.All.All f ks) where
  decodeFrom = decAllV

--------------------------------------------------------------------------------
--          Decoding Tables
--------------------------------------------------------------------------------

readTable' :
     {auto _ : TSVDecoder a}
  -> SnocList a
  -> Position
  -> (cs : List Char)
  -> (0 acc : SuffixAcc cs)
  -> Either (Bounded $ InnerError e) (List a)
readTable' sx pos []              _      = Right (sx <>> [])
readTable' sx pos xs              (SA r) = case decodeFrom {a} xs of
  Succ v xs2 @{p} => case xs2 of
    []               => Right (sx <>> [v])
    '\n' ::       t2 => readTable' (sx :< v) (incLine pos) t2 r
    '\r'::'\n' :: t2 => readTable' (sx :< v) (incLine pos) t2 r
    c :: _           =>
      let bs := Bounds.oneChar (move pos p)
       in if isControl c then Left $ B (InvalidControl c) bs
          else unexpected (B (show c) bs)
  Fail x y z => Left (boundedErr pos x y z)

export
readTable :
     {auto _ : TSVDecoder a}
  -> Origin
  -> String
  -> Either (ParseError e) (List a)
readTable o s =
  mapFst (toParseError o s) (readTable' [<] begin (unpack s) suffixAcc)
