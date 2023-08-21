module Text.TSV.Encoder

import Data.List
import Data.String
import Data.Vect
import Data.Vect.Quantifiers as VQ
import Data.List.Quantifiers as LQ

%default total

--------------------------------------------------------------------------------
--          Interface
--------------------------------------------------------------------------------

||| Encodes a multi-field value as a list of strings.
||| These can then be written
||| to a file, seperated by a tab
public export
interface TSVEncoder a where
  constructor MkTSVEncoder
  encodeOnto : SnocList String -> a -> SnocList String

--------------------------------------------------------------------------------
--          Primitives
--------------------------------------------------------------------------------

export
TSVEncoder () where encodeOnto sc v = sc :< show v

export
TSVEncoder Bits8 where encodeOnto sc v = sc :< show v

export
TSVEncoder Bits16 where encodeOnto sc v = sc :< show v

export
TSVEncoder Bits32 where encodeOnto sc v = sc :< show v

export
TSVEncoder Bits64 where encodeOnto sc v = sc :< show v

export
TSVEncoder Int8 where encodeOnto sc v = sc :< show v

export
TSVEncoder Int16 where encodeOnto sc v = sc :< show v

export
TSVEncoder Int32 where encodeOnto sc v = sc :< show v

export
TSVEncoder Int64 where encodeOnto sc v = sc :< show v

export
TSVEncoder Int where encodeOnto sc v = sc :< show v

export
TSVEncoder Integer where encodeOnto sc v = sc :< show v

export
TSVEncoder Nat where encodeOnto sc v = sc :< show v

export
TSVEncoder String where encodeOnto sc v = sc :< v

export
TSVEncoder Double where encodeOnto sc v = sc :< show v

export
TSVEncoder Bool where encodeOnto sc v = sc :< show v

--------------------------------------------------------------------------------
--          Derived Encoders
--------------------------------------------------------------------------------

export
TSVEncoder a => TSVEncoder (Maybe a) where
  encodeOnto sc Nothing  = sc :< ""
  encodeOnto sc (Just v) = encodeOnto sc v

export
TSVEncoder a => TSVEncoder b => TSVEncoder (a,b) where
  encodeOnto sc (va, vb) = encodeOnto (encodeOnto sc va) vb

--------------------------------------------------------------------------------
--          HList and HVect
--------------------------------------------------------------------------------

encAll :
     {0 ks : List k}
  -> {auto _ : All (TSVEncoder . f) ks}
  -> SnocList String
  -> All f ks
  -> SnocList String
encAll           ss []      = ss
encAll @{_ :: _} ss (v::vs) = encAll (encodeOnto ss v) vs

encAllV :
     {0 ks : Vect n k}
  -> {auto _ : All (TSVEncoder . f) ks}
  -> SnocList String
  -> All f ks
  -> SnocList String
encAllV           ss []      = ss
encAllV @{_ :: _} ss (v::vs) = encAllV (encodeOnto ss v) vs

export %inline
All (TSVEncoder . f) ks => TSVEncoder (LQ.All.All f ks) where
  encodeOnto sc vs = encAll sc vs

export %inline
All (TSVEncoder . f) ks => TSVEncoder (VQ.All.All f ks) where
  encodeOnto sc vs = encAllV sc vs

--------------------------------------------------------------------------------
--          Convertings values to rows and tables
--------------------------------------------------------------------------------

export
toRow : TSVEncoder a => a -> String
toRow v =
  let ss := encodeOnto [<] v <>> []
   in concat $ intersperse "\t" ss

export %inline
toTable : TSVEncoder a => List a -> String
toTable = unlines . map toRow
