module Data.Bool.Rewrite

import public Data.Bool

%default total

public export %inline
swapOr : {0 x,y : _} -> (0 p : Bool -> Type) -> p (x || y) -> p (y || x)
swapOr p v = replace {p} (orCommutative x y) v

public export %inline
orSame : {0 x : _} -> (0 p : Bool -> Type) -> p (x || x) -> p x
orSame p v = replace {p} (orSameNeutral x) v

public export %inline
orTrue : {0 x : _} -> (0 p : Bool -> Type) -> p (x || True) -> p True
orTrue p v = replace {p} (orTrueTrue x) v

public export %inline
orFalse : {0 x : _} -> (0 p : Bool -> Type) -> p (x || False) -> p x
orFalse p v = replace {p} (orFalseNeutral x) v

public export %inline
swapAnd : {0 x,y : _} -> (0 p : Bool -> Type) -> p (x && y) -> p (y && x)
swapAnd p v = replace {p} (andCommutative x y) v

public export %inline
andSame : {0 x : _} -> (0 p : Bool -> Type) -> p (x && x) -> p x
andSame p v = replace {p} (andSameNeutral x) v

public export %inline
andTrue : {0 x : _} -> (0 p : Bool -> Type) -> p (x && True) -> p x
andTrue p v = replace {p} (andTrueNeutral x) v

public export %inline
andFalse : {0 x : _} -> (0 p : Bool -> Type) -> p (x && False) -> p False
andFalse p v = replace {p} (andFalseFalse x) v
