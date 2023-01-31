module Test.Lex.Idris2.Gen

import Text.Lex.Idris2.Common
import Text.Lex.Idris2.Source
import Data.List
import Data.Vect
import Hedgehog

%default total

--------------------------------------------------------------------------------
--          Whitespace
--------------------------------------------------------------------------------

export
spaces : Gen String
spaces = string (linear 1 3) (element [' ', '\t', '\n', '\r'])

export
optSpaces : Gen String
optSpaces = frequency [(5,spaces), (1,pure "")]

export
spaced : List (Gen String) -> Gen String
spaced gs = concat <$> sequence (intersperse spaces gs)

export
maybeSpaced : List (Gen String) -> Gen String
maybeSpaced gs = concat <$> sequence (intersperse optSpaces gs)

export
nonControl : Gen Char
nonControl = adj <$> unicode
  where
    adj : Char -> Char
    adj c = if isControl c then ' ' else c

--------------------------------------------------------------------------------
--          Comments
--------------------------------------------------------------------------------

export
comment : Gen String
comment = (\s => "--\{s}\n") <$> string (linear 0 20)  nonControl

export
docComment : Gen String
docComment = (\s => "|||\{s}\n") <$> string (linear 0 20)  nonControl

export
blockComment : Gen String
blockComment = [| block any any any |]
  where
    any : Gen String
    any = string (linear 0 20) unicode

    block : String -> String -> String -> String
    block x y z = "{-x{-y-}z-}"

--------------------------------------------------------------------------------
--          Pragmas
--------------------------------------------------------------------------------

export
cgDirective : Gen String
cgDirective = ("%cg" ++) <$> choice [complex,simple]
  where
    nonBrace : Gen Char
    nonBrace = (\case {'{' => ' '; c => c}) <$> unicode

    spaceChars,name,complex,simple,rest : Gen String
    spaceChars = string (linear 0 5) (pure ' ')

    name = string (linear 1 10) alphaNum

    simple = string (linear 0 20) nonControl

    rest = (\x => "{\{x}}") <$> string (linear 0 20) nonBrace

    complex = pure $ !spaceChars ++ !name ++ !spaceChars ++ !rest

--------------------------------------------------------------------------------
--          Identifiers
--------------------------------------------------------------------------------

identUnicode : Gen Char
identUnicode = adj <$> unicode
  where
    adj : Char -> Char
    adj c = if c > '\160' then c else '¡'

export
identStart : Flavour -> Gen Char
identStart Capitalised =
  frequency [(10, upper), (1, pure '_'), (2, identUnicode)]
identStart AllowDashes =
  lower
identStart Normal      =
  frequency [(10, alpha), (1, pure '_'), (2, identUnicode)]

export
identTrailing : Flavour -> Gen Char
identTrailing f =
  let sym :=
    if f == AllowDashes then element ['-','\'','_'] else element ['\'', '_']
   in frequency [(10, alphaNum), (1,sym), (2, identUnicode)]

export
ident : Flavour -> Gen String
ident f =
  [| (\h,t => pack $ h :: t)
     (identStart f)
     (list (linear 0 20) (identTrailing f)) |]

export
identNormal : Gen String
identNormal = ident Normal

export
hole : Gen String
hole = ("?" ++) <$> identNormal

export
dotIdent : Gen String
dotIdent = ("." ++) <$> identNormal

export
pragma : Gen String
pragma = ("%" ++) <$> identNormal

export
identAllowDashes : Gen String
identAllowDashes = ident AllowDashes

export
namespacedIdent : Gen String
namespacedIdent =
  [| (\h,t => concat . intersperse "." $ t ++ [h])
     identNormal
     (list (linear 0 4) (ident Capitalised)) |]

--------------------------------------------------------------------------------
--          Packages
--------------------------------------------------------------------------------

export
version : Gen String
version = choice [lower, upper, between, exact, pure ""]
  where lower, upper, between,exact,vers : Gen String

        prefixVersion : String -> Maybe String -> String -> String
        prefixVersion a b c = a ++ fromMaybe "" b ++ c

        vv : String -> Gen String
        vv s = maybeSpaced [pure s, vers]

        vers = concat . intersperse "." . map show <$>
               list (linear 1 4) (nat $ linear 0 100)

        lower = choice [ vv ">", vv ">=" ]
        upper = choice [ vv "<", vv "<=" ]
        between = maybeSpaced [lower, pure "&&", upper]
        exact =  vv "=="

fld : String -> Gen String -> Gen String
fld nm g = spaced [pure "", pure nm, pure "=", g]

stringLit : Gen String
stringLit = quote [<'"'] . unpack <$> string (linear 0 20) unicode
  where quote : SnocList Char -> List Char -> String
        quote sc (x :: xs) = case x of
          '\\' => quote (sc :< '\\' :< '\\') xs
          '\n' => quote (sc :< '\\' :< '\n') xs
          '\r' => quote (sc :< '\\' :< '\r') xs
          '\t' => quote (sc :< '\\' :< '\t') xs
          '"'  => quote (sc :< '\\' :< '"') xs
          c    => if isControl c then quote sc xs else quote (sc :< c) xs
        quote sc []        = cast (sc :< '"')

export
pkgField : Gen String
pkgField = choice [
    fld "author" stringLit
  , fld "maintainers" stringLit
  , fld "license" stringLit
  , fld "brief" stringLit
  , fld "readme" stringLit
  , fld "sourceloc" stringLit
  , fld "bugtracker" stringLit
  , fld "executable" stringLit
  , fld "opts" stringLit
  , fld "sourcedir" stringLit
  , fld "builddir" stringLit
  , fld "outputdir" stringLit
  , fld "prebuild" stringLit
  , fld "postbuild" stringLit
  , fld "preinstall" stringLit
  , fld "postinstall" stringLit
  , fld "preclean" stringLit
  , fld "postclean" stringLit
  , fld "langversion" version
  ]

pkgRest : Gen String
pkgRest = concat <$> list (linear 0 20) pkgField

pkgName : Gen String
pkgName = spaced [pure "package", identAllowDashes]

export
package : Gen String
package = [| pkgName ++ pkgRest |]

--------------------------------------------------------------------------------
--          Keywords
--------------------------------------------------------------------------------

export
sourceKeyword : Gen String
sourceKeyword = element (fromList keywords)

export
debugInfo : Gen String
debugInfo = interpolate <$> element [DebugLoc, DebugFile, DebugLine, DebugCol]

--------------------------------------------------------------------------------
--          Source
--------------------------------------------------------------------------------

export
src : String
src = ##"""
  module Test.Lex.Idris2.Gen
  
  import Text.Lex.Idris2.Common
  import Text.Lex.Idris2.Source
  import Data.List
  import Data.Vect
  import Hedgehog
  
  %default total
  
  --------------------------------------------------------------------------------
  --          Whitespace
  --------------------------------------------------------------------------------
  
  export
  spaces : Gen String
  spaces = string (linear 1 3) (element [' ', '\t', '\n', '\r'])
  
  export
  optSpaces : Gen String
  optSpaces = frequency [(5,spaces), (1,pure "")]
  
  export
  spaced : List (Gen String) -> Gen String
  spaced gs = concat <$> sequence (intersperse spaces gs)
  
  export
  maybeSpaced : List (Gen String) -> Gen String
  maybeSpaced gs = concat <$> sequence (intersperse optSpaces gs)
  
  export
  nonControl : Gen Char
  nonControl = adj <$> unicode
    where
      adj : Char -> Char
      adj c = if isControl c then ' ' else c
  
  --------------------------------------------------------------------------------
  --          Comments
  --------------------------------------------------------------------------------
  
  export
  comment : Gen String
  comment = (\s => "--\{s}\n") <$> string (linear 0 20)  nonControl
  
  export
  docComment : Gen String
  docComment = (\s => "|||\{s}\n") <$> string (linear 0 20)  nonControl
  
  export
  blockComment : Gen String
  blockComment = [| block any any any |]
    where
      any : Gen String
      any = string (linear 0 20) unicode
  
      block : String -> String -> String -> String
      block x y z = "{-x{-y-}z-}"
  
  --------------------------------------------------------------------------------
  --          Pragmas
  --------------------------------------------------------------------------------
  
  export
  cgDirective : Gen String
  cgDirective = ("%cg" ++) <$> choice [complex,simple]
    where
      nonBrace : Gen Char
      nonBrace = (\case {'{' => ' '; c => c}) <$> unicode
  
      spaceChars,name,complex,simple,rest : Gen String
      spaceChars = string (linear 0 5) (pure ' ')
  
      name = string (linear 1 10) alphaNum
  
      simple = string (linear 0 20) nonControl
  
      rest = (\x => "{\{x}}") <$> string (linear 0 20) nonBrace
  
      complex = pure $ !spaceChars ++ !name ++ !spaceChars ++ !rest
  
  --------------------------------------------------------------------------------
  --          Identifiers
  --------------------------------------------------------------------------------
  
  identUnicode : Gen Char
  identUnicode = adj <$> unicode
    where
      adj : Char -> Char
      adj c = if c > '\160' then c else '¡'
  
  export
  identStart : Flavour -> Gen Char
  identStart Capitalised =
    frequency [(10, upper), (1, pure '_'), (2, identUnicode)]
  identStart AllowDashes =
    lower
  identStart Normal      =
    frequency [(10, alpha), (1, pure '_'), (2, identUnicode)]
  
  export
  identTrailing : Flavour -> Gen Char
  identTrailing f =
    let sym :=
      if f == AllowDashes then element ['-','\'','_'] else element ['\'', '_']
     in frequency [(10, alphaNum), (1,sym), (2, identUnicode)]
  
  export
  ident : Flavour -> Gen String
  ident f =
    [| (\h,t => pack $ h :: t)
       (identStart f)
       (list (linear 0 20) (identTrailing f)) |]
  
  export
  identNormal : Gen String
  identNormal = ident Normal
  
  export
  hole : Gen String
  hole = ("?" ++) <$> identNormal
  
  export
  dotIdent : Gen String
  dotIdent = ("." ++) <$> identNormal
  
  export
  pragma : Gen String
  pragma = ("%" ++) <$> identNormal
  
  export
  identAllowDashes : Gen String
  identAllowDashes = ident AllowDashes
  
  export
  namespacedIdent : Gen String
  namespacedIdent =
    [| (\h,t => concat . intersperse "." $ t ++ [h])
       identNormal
       (list (linear 0 4) (ident Capitalised)) |]
  
  --------------------------------------------------------------------------------
  --          Packages
  --------------------------------------------------------------------------------
  
  export
  version : Gen String
  version = choice [lower, upper, between, exact, pure ""]
    where lower, upper, between,exact,vers : Gen String
  
          prefixVersion : String -> Maybe String -> String -> String
          prefixVersion a b c = a ++ fromMaybe "" b ++ c
  
          vv : String -> Gen String
          vv s = maybeSpaced [pure s, vers]
  
          vers = concat . intersperse "." . map show <$>
                 list (linear 1 4) (nat $ linear 0 100)
  
          lower = choice [ vv ">", vv ">=" ]
          upper = choice [ vv "<", vv "<=" ]
          between = maybeSpaced [lower, pure "&&", upper]
          exact =  vv "=="
  
  fld : String -> Gen String -> Gen String
  fld nm g = spaced [pure "", pure nm, pure "=", g]
  
  stringLit : Gen String
  stringLit = quote [<'"'] . unpack <$> string (linear 0 20) unicode
    where quote : SnocList Char -> List Char -> String
          quote sc (x :: xs) = case x of
            '\\' => quote (sc :< '\\' :< '\\') xs
            '\n' => quote (sc :< '\\' :< '\n') xs
            '\r' => quote (sc :< '\\' :< '\r') xs
            '\t' => quote (sc :< '\\' :< '\t') xs
            '"'  => quote (sc :< '\\' :< '"') xs
            c    => if isControl c then quote sc xs else quote (sc :< c) xs
          quote sc []        = pack (sc :< '"')
  
  export
  pkgField : Gen String
  pkgField = choice [
      fld "author" stringLit
    , fld "maintainers" stringLit
    , fld "license" stringLit
    , fld "brief" stringLit
    , fld "readme" stringLit
    , fld "sourceloc" stringLit
    , fld "bugtracker" stringLit
    , fld "executable" stringLit
    , fld "opts" stringLit
    , fld "sourcedir" stringLit
    , fld "builddir" stringLit
    , fld "outputdir" stringLit
    , fld "prebuild" stringLit
    , fld "postbuild" stringLit
    , fld "preinstall" stringLit
    , fld "postinstall" stringLit
    , fld "preclean" stringLit
    , fld "postclean" stringLit
    , fld "langversion" version
    ]
  
  pkgRest : Gen String
  pkgRest = concat <$> list (linear 0 20) pkgField
  
  pkgName : Gen String
  pkgName = spaced [pure "package", identAllowDashes]
  
  export
  package : Gen String
  package = [| pkgName ++ pkgRest |]
  
  --------------------------------------------------------------------------------
  --          Keywords
  --------------------------------------------------------------------------------
  
  export
  sourceKeyword : Gen String
  sourceKeyword = element (fromList keywords)
  
  export
  debugInfo : Gen String
  debugInfo = interpolate <$> element [DebugLoc, DebugFile, DebugLine, DebugCol]
  
  --------------------------------------------------------------------------------
  --          Source
  --------------------------------------------------------------------------------

  src : String
  src = #"""
    this is a test
    with some stuff
    """#
  """##
