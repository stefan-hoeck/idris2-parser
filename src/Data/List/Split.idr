module Data.List.Split

import Data.List.Suffix

%default total

public export
data Split :
     (strict : Bool)
  -> (sa : SnocList a)
  -> (as,orig : List a)
  -> Type where
  Init  : Split False [<] as as
  Shift : Split b1 sa (h :: t) xs -> Split b2 (sa :< h) t xs

0 suffix : Split b sa as o -> Suffix_ b as o
suffix Init       = Same
suffix (Shift x)  = weakenS $ consLeft $ suffix x

--------------------------------------------------------------------------------
--          Rec
--------------------------------------------------------------------------------

||| Result of running a lexer once: The lexer either stops, when
||| can no longer consume any characters, or it consumed some
||| characters and returns (a possibly `strict`) suffix of the
||| input character sequence.
public export
data Rec : (strict  : Bool) -> (o : List t) -> Type where
  Stop : Rec s o
  Res :  (sc    : SnocList t)
      -> (toks  : List t)
      -> (0 prf : Split b sc toks o)
      -> Rec b cs

||| this is the identity at runtim
export
mapPrf :
     (0 f :
          {t     : Type}
       -> {st    : SnocList t}
       -> {ts,o  : List t}
       -> {b1,b2 : Bool}
       -> Split b1 st ts o
       -> Split b2 st ts o
     )
  -> Rec s1 o
  -> Rec s2 o
mapPrf f Stop              = Stop
mapPrf f (Res sc toks prf) = Res sc toks (f prf)

-- namespace Rec
--   export
--   (<|>) : Rec b1 cs -> Lazy (Rec b2 cs) -> Rec (b1 && b2) cs
--   (<|>) r@(Res _ _ _) _  = mapPrf and1 r
--   (<|>) Stop          r  = mapPrf and2 r
