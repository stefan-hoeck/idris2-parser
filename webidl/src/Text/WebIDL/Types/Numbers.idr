module Text.WebIDL.Types.Numbers

import Derive.Prelude

%default total

%language ElabReflection

--------------------------------------------------------------------------------
--          IntLit
--------------------------------------------------------------------------------

hexDigit : Integer -> Char
hexDigit n = if n < 10 then chr (48 + cast n) else chr (97 + cast (n - 10))

digs :
     (base : Integer)
  -> {auto 0 _ : (base > 0) === True}
  -> List Char
  -> Integer
  -> String
digs b [] 0 = "0"
digs b cs 0 = pack cs
digs b cs n = digs b (hexDigit (mod n b) :: cs) (assert_smaller n $ div n b)

||| An integer literal in hexadecimal, octal, or decimal representation.
||| The code generator will use the same representation when
||| generating code for constants and default values.
public export
data IntLit = Hex Nat | Oct Nat | I Integer

%runElab derive "IntLit" [Show, Eq]

export
Interpolation IntLit where
  interpolate (Hex k) = "0x\{digs 16 [] $ cast k}"
  interpolate (Oct k) = digs 8 ['0'] $ cast k
  interpolate (I i)   = show i

--------------------------------------------------------------------------------
--          Floating Point Literals
--------------------------------------------------------------------------------

||| The sign of a floating point literal.
public export
data Signum = Plus | Minus

%runElab derive "Signum" [Eq,Show]

||| A parsed floating point literal.
|||
||| A floating point literal is either one of three
||| special values (`NaN`, `Infinity`, or `-Infinity`)
||| or a decimal floating point number (`NoExp`: dot is
||| mandatory), or a float in scientific notation (`Exp`:
||| dot is optional).
|||
||| The main focus of this data type is one of
||| preserving information. Encoding a `FloatLit` should
||| yield (almost) exactly the same literal as the one
||| encountered during parsin with two minor exceptions:
||| a) The encoded literal will always use a lowercase 'e' as
||| the delimiter for the exponent and b) in case of a
||| positive exponent, there will not be a '+' in the
||| encoded literal.
public export
data FloatLit : Type where
  ||| Floating point number in scientific notation.
  |||
  ||| Example: `-12.10e10`
  Exp :  (beforeDot : Integer)
      -> (afterDot  : Maybe Nat)
      -> (exp       : Integer)
      -> FloatLit

  ||| Floating point number without exponent.
  |||
  ||| Example: `-12.1002`
  NoExp :  (beforeDot : Integer)
        -> (afterDot  : Nat)
        -> FloatLit

  ||| Corresponds to the WebIDL keyword `Infinity`
  Infinity         : FloatLit

  ||| Corresponds to the WebIDL keyword `-Infinity`
  NegativeInfinity : FloatLit

  ||| Corresponds to the WebIDL keyword `NaN`
  NaN              : FloatLit

%runElab derive "FloatLit" [Show,Eq]

export
Interpolation FloatLit where
  interpolate (Exp bd (Just ad) ex) = "\{show bd}.\{show ad}e\{show ex}"
  interpolate (Exp bd Nothing ex)   = "\{show bd}e\{show ex}"
  interpolate (NoExp bd ad)         = "\{show bd}.\{show ad}"
  interpolate Infinity              = "Infinity"
  interpolate NegativeInfinity      = "-Infinity"
  interpolate NaN                   = "NaN"
