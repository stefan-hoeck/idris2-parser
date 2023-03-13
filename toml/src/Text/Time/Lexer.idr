module Text.Time.Lexer

import Data.Maybe
import Data.Time.Time
import Text.Lex.Manual

public export
readInt : Integer -> List Char -> Maybe Integer
readInt n []       = Just n
readInt n (h :: t) =
  if isDigit h then readInt (n*10 + cast (digit h)) t else Nothing

public export %inline
readYear : List Char -> Maybe Year
readYear cs = readInt 0 cs >>= refineYear

public export %inline
readMonth : List Char -> Maybe Month
readMonth cs = readInt 0 cs >>= intToMonth

public export %inline
readDay : {m : _} -> List Char -> Maybe (Day m)
readDay cs = readInt 0 cs >>= refineDay {m}

public export %inline
readHour : List Char -> Maybe Hour
readHour cs = readInt 0 cs >>= refineHour

public export %inline
readMinute : List Char -> Maybe Minute
readMinute cs = readInt 0 cs >>= refineMinute

public export %inline
readSecond : List Char -> Maybe Second
readSecond cs = readInt 0 cs >>= refineSecond

--------------------------------------------------------------------------------
--          Date
--------------------------------------------------------------------------------

export
date : StrictTok e Date
date (y1::y2::y3::y4::'-'::m1::m2::'-'::d1::d2::t) =
  let Just y := readYear [y1,y2,y3,y4] | Nothing => unknownRange p t
      Just m := readMonth [m1,m2]      | Nothing => unknownRange p t
      Just d := readDay {m} [d1,d2]    | Nothing => unknownRange p t
   in Succ (MkDate y m d) t
date xs = fail p

--------------------------------------------------------------------------------
--          LocalTime
--------------------------------------------------------------------------------

toMS : (digs,cur : Nat) -> Maybe MicroSecond
toMS 0     cur = refineMicroSecond (cast cur)
toMS (S k) cur = toMS k (cur * 10)

export
prec' : Hour -> Minute -> Second -> (digs,cur : Nat) -> SafeTok LocalTime
prec' h m s digs cur (d::t) = case isDigit d of
  False => Succ (LT h m s $ toMS digs cur) (d::t)
  True  =>  case digs of
    Z   => prec' h m s 0 cur t
    S k => prec' h m s k (cur * 10 + digit d) t
prec' h m s digs cur [] = Succ (LT h m s $ toMS digs cur) []

export
prec : Hour -> Minute -> Second -> AutoTok e LocalTime
prec h m s ('.'::d::t) =
  if isDigit d then prec' h m s 5 (digit d) t else unknownRange p t
prec h m s xs = Succ (LT h m s Nothing) xs

export
localTime : StrictTok e LocalTime
localTime (h1::h2::':'::m1::m2::':'::s1::s2::t) =
  let Just hh := readHour   [h1,h2] | Nothing => unknownRange p t
      Just mm := readMinute [m1,m2] | Nothing => unknownRange p t
      Just ss := readSecond [s1,s2] | Nothing => unknownRange p t
   in prec hh mm ss t
localTime (h1::h2::':'::m1::m2::t) =
  let Just hh := readHour   [h1,h2] | Nothing => unknownRange p t
      Just mm := readMinute [m1,m2] | Nothing => unknownRange p t
   in prec hh mm 0 t
localTime xs = fail p

--------------------------------------------------------------------------------
--          OffsetTime
--------------------------------------------------------------------------------

sign : Char -> Maybe Sign
sign '-' = Just Minus
sign '+' = Just Plus
sign _   = Nothing

offset : AutoTok e Offset
offset ('Z'::t) = Succ Z t
offset ('z'::t) = Succ Z t
offset (s::h1::h2::':'::m1::m2::t) =
  let Just ss := sign s | Nothing => unknownRange p t
      Just hh :=readHour [h1,h2]   | Nothing => unknownRange p t
      Just mm :=readMinute [m1,m2] | Nothing => unknownRange p t
   in Succ (O ss hh mm) t
offset xs = unknownRange p xs

export
offsetTime : StrictTok e OffsetTime
offsetTime xs =
  let Succ lt ys := localTime xs | Fail s e r => Fail s e r
   in OT lt <$> offset ys

--------------------------------------------------------------------------------
--          AnyTime
--------------------------------------------------------------------------------

anyTimeOnly : StrictTok e (Either LocalTime OffsetTime)
anyTimeOnly xs =
  let Succ lt ys := localTime xs  | Fail s e r => Fail s e r
      Succ o  zs := offset {e} ys | Fail {} => Succ (Left lt) ys
   in Succ (Right $ OT lt o) zs

%inline
addDate : Date -> Either LocalTime OffsetTime -> AnyTime
addDate x = either (ATLocalDateTime . LDT x) (ATOffsetDateTime . ODT x)

export
anyTime : StrictTok e AnyTime
anyTime xs =
  let Succ dt ys := date {e} xs | Fail {} => ATLocalTime <$> localTime xs
   in case ys of
        'T'::t => addDate dt <$> autoTok anyTimeOnly t
        't'::t => addDate dt <$> autoTok anyTimeOnly t
        ' '::t =>
          let Succ at zs := autoTok anyTimeOnly {e} t
                | Fail {} => Succ (ATDate dt) (' ' :: t)
           in Succ (addDate dt at) zs
        _      => Succ (ATDate dt) ys
