module Text.Time.Lex

import Data.Time.Time
import Text.Lex.Manual

public export
readNat : Nat -> List Char -> Maybe Nat
readNat n []       = Just n
readNat n (h :: t) = if isDigit h then readNat (n*10 + digit h) t else Nothing

--------------------------------------------------------------------------------
--          Date
--------------------------------------------------------------------------------

export
date : OntoTok Char Date
date (y1::y2::y3::y4::'-'::m1::m2::'-'::d1::d2::t) =
  let Just y := readNat 0 [y1,y2,y3,y4] >>= refineYear
        | Nothing => unknownRange p t
      Just m := readNat 0 [m1,m2] >>= natToMonth
        | Nothing => unknownRange p t
      Just d := readNat 0 [d1,d2] >>= refineDay {m}
        | Nothing => unknownRange p t
   in Succ (MkDate y m d) t
date xs = unknown xs

--------------------------------------------------------------------------------
--          LocalTime
--------------------------------------------------------------------------------

toMS : (digs,cur : Nat) -> Maybe MilliSecond
toMS 0     cur = refineMilliSecond cur
toMS (S k) cur = toMS k (cur * 10)

export
prec' : Hour -> Minute -> Second -> (digs,cur : Nat) -> SafeTok Char LocalTime
prec' h m s digs cur (d::t) = case isDigit d of
  False => Succ (LT h m s $ toMS digs cur) (d::t)
  True  =>  case digs of
    Z   => prec' h m s 0 cur t
    S k => prec' h m s k (cur * 10 + digit d) t
prec' h m s digs cur [] = Succ (LT h m s $ toMS digs cur) []

export
prec : Hour -> Minute -> Second -> AutoTok Char LocalTime
prec h m s ('.'::d::t) =
  if isDigit d then prec' h m s 2 (digit d) t else unknown (d::t)
prec h m s xs = Succ (LT h m s Nothing) xs

export
localTime : OntoTok Char LocalTime
localTime (h1::h2::':'::m1::m2::':'::s1::s2::t) =
  let Just hh := readNat 0 [h1,h2] >>= refineHour
        | Nothing => unknownRange p t
      Just mm := readNat 0 [m1,m2] >>= refineMinute
        | Nothing => unknownRange p t
      Just ss := readNat 0 [s1,s2] >>= refineSecond
        | Nothing => unknownRange p t
   in prec hh mm ss t
localTime xs = unknown xs

--------------------------------------------------------------------------------
--          OffsetTime
--------------------------------------------------------------------------------

sign : Char -> Maybe Sign
sign '-' = Just Minus
sign '+' = Just Plus
sign _   = Nothing

offset : AutoTok Char Offset
offset ('Z'::t) = Succ Z t
offset (s::h1::h2::':'::m1::m2::t) =
  let Just ss := sign s | Nothing => unknownRange p t
      Just hh :=readNat 0 [h1,h2] >>= refineHour
        | Nothing => unknownRange p t
      Just mm :=readNat 0 [m1,m2] >>= refineMinute
        | Nothing => unknownRange p t
   in Succ (O ss hh mm) t

offset xs = unknownRange p xs

export
offsetTime : OntoTok Char OffsetTime
offsetTime xs =
  let Succ lt ys := localTime xs | Fail s e r => Fail s e r
   in OT lt <$> offset ys
