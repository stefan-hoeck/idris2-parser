module Text.Parse.Core

import Data.List.Suffix

%default total

--------------------------------------------------------------------------------
--          Parsing Results
--------------------------------------------------------------------------------

||| Result of running a parser.
public export
data Res : (strict  : Bool) -> (ts : List t) -> (e,a : type) -> Type where
  Err  : (err : e) -> Res b ts e a

  Pure : (res : a) -> (toks : List t) -> Res False toks e a

  Succ :  (res   : a)
       -> (toks  : List t)
       -> (0 prf : StrictSuffix toks ts)
       -> Res b ts e a

public export
succ : Res b ts e a -> (0 p : StrictSuffix ts ts') -> Res b' ts' e a
succ (Err err) p           = Err err
succ (Pure res ts) p       = Succ res ts p
succ (Succ res toks prf) p = Succ res toks (prf ~> p)

--------------------------------------------------------------------------------
--          Proofs
--------------------------------------------------------------------------------

0 andFalse : False === (b && Delay False)
andFalse {b = True}  = Refl
andFalse {b = False} = Refl

0 orFalse : (b || Delay False) === b
orFalse {b = True}  = Refl
orFalse {b = False} = Refl

--------------------------------------------------------------------------------
--          Grammar
--------------------------------------------------------------------------------

public export
0 inf : Bool -> Type -> Type
inf False y = y
inf True  y = Inf y

public export
data Grammar : (strict : Bool) -> (t,e,a : type) -> Type where
  Lift    : ((ts : List t) -> Res s ts e a) -> Grammar s t e a
  SeqEat  : Grammar True t e a -> Inf (a -> Grammar b2 t e b) -> Grammar True t e b
  ThenEat : Grammar True t e a -> Inf (Grammar b2 t e b) -> Grammar True t e b
  Seq     : Grammar b1 t e a -> (a -> Grammar b2 t e b) -> Grammar (b1 || b2) t e b
  Then    : Grammar b1 t e a -> (Grammar b2 t e b) -> Grammar (b1 || b2) t e b
  Catch   : Grammar b1 t e a -> (e -> Grammar b2 t e a) -> Grammar (b1 && b2) t e a

public export %inline
(>>=) :
     {b1,b2 : _}
  -> Grammar b1 t e a
  -> inf b1 (a -> Grammar b2 t e b)
  -> Grammar (b1 || b2) t e b
(>>=) {b1 = False} = Seq
(>>=) {b1 = True}  = SeqEat

public export %inline
(>>) :
     {b1,b2 : _}
  -> Grammar b1 t e ()
  -> inf b1 (Grammar b2 t e b)
  -> Grammar (b1 || b2) t e b
(>>) {b1 = False} = Then
(>>) {b1 = True}  = ThenEat

public export %inline
(<|>) :
     {0 b1,b2 : Bool}
  -> {0 t,e,a : Type}
  -> Grammar b1 t e a
  -> Lazy (Grammar b2 t e a)
  -> Grammar (b1 && b2) t e a
x <|> y = Catch x (\_ => y)

public export %inline
fail : (err : e) -> Grammar b t e a
fail err = Lift $ \ts => Err err

public export %inline
pure : (res : a) -> Grammar False t e a
pure = Lift . Pure

public export
Functor (Grammar s t e) where
  map f g = replace {p = \x => Grammar x t e b} orFalse $ Seq g (pure . f)

public export %inline
(<*>) :
      Grammar b1 t e (a -> b)
   -> Grammar b2 t e a
   -> Grammar (b1 || b2) t e b
(<*>) x y = Seq x (\f => map f y)

public export
some : Grammar True t e a -> Grammar True t e (List a)
some g = Core.do
  v  <- g
  vs <- some g <|> pure []
  pure (v :: vs)

public export
many : Grammar True t e a -> Grammar False t e (List a)
many g = some g <|> pure []

prs :
     Grammar b t e a
  -> (ts : List t)
  -> (0 acc : SuffixAcc ts)
  -> Res b ts e a
prs (Lift f) ts _ = f ts
prs (SeqEat g f) ts (Access rec) = case prs g ts (Access rec) of
  Err e            => Err e
  Succ res ts' prf => succ (prs (f res) ts' (rec ts' prf)) prf
prs (Seq g f) ts acc@(Access rec) = case prs g ts acc of
  Pure res ts       => prs (f res) ts acc
  Succ res toks prf => succ (prs (f res) toks (rec toks prf)) prf
  Err err           => Err err
prs (ThenEat g f) ts (Access rec) = case prs g ts (Access rec) of
  Succ _ ts' prf => succ (prs f ts' (rec ts' prf)) prf
  Err e          => Err e
prs (Then g f) ts acc@(Access rec) = case prs g ts acc of
  Pure _ ts       => prs f ts acc
  Succ _ toks prf => succ (prs f toks (rec toks prf)) prf
  Err err         => Err err
prs (Catch x f) ts acc = case prs x ts acc of
  Pure res ts       => Pure res ts
  Succ res toks prf => Succ res toks prf
  Err err           => case prs (f err) ts acc of
    Succ res toks prf => Succ res toks prf
    Pure res ts       =>
      replace {p = \bo => Res bo ts e a} andFalse $ Pure res ts
    Err err           => Err err

export %inline
parse : Grammar True t e a -> (ts : List t) -> Res True ts e a
parse g ts = prs g ts (ssAcc _)
