module Text.Lex.Idris2.Source

import Core.Name
import Core.Name.Namespace.Extra
import Data.Either
import Derive.Prelude
import Text.Lex.Idris2.Common
import public Text.Lex.Tokenizer

%hide Language.Reflection.TT.Namespace
%default total
%language ElabReflection

--------------------------------------------------------------------------------
--          Types
--------------------------------------------------------------------------------

public export
data IsMultiline = Multi | Single

%runElab derive "IsMultiline" [Show, Eq]

public export
data DebugInfo =
    DebugLoc
  | DebugFile
  | DebugLine
  | DebugCol

%runElab derive "DebugInfo" [Show, Eq]

export
Interpolation DebugInfo where
  interpolate DebugLoc  = "__LOC__"
  interpolate DebugFile = "__FILE__"
  interpolate DebugLine = "__LINE__"
  interpolate DebugCol  = "__COL__"

public export
data Token
  -- Literals
  = CharLit String
  | DoubleLit Double
  | IntegerLit Integer
  -- String
  | StringBegin IsMultiline -- Whether is multiline string
  | StringEnd
  | InterpBegin
  | InterpEnd
  | StringLit Nat String
  -- Identifiers
  | HoleIdent String
  | Ident String
  | DotSepIdent Namespace String -- ident.ident
  | DotIdent String               -- .ident
  | Symbol String
  -- Whitespace
  | Space
  -- Comments
  | Comment
  | DocComment String
  -- Special
  | CGDirective String
  | EndInput
  | Keyword String
  | Pragma String
  | MagicDebugInfo DebugInfo
  | Unrecognised String

%runElab derive "Token" [Show,Eq]

--------------------------------------------------------------------------------
--          Lexers
--------------------------------------------------------------------------------

data CommentState =
    Block -- arbitrary position in a block comment
  | Opening -- part of opening sequence: `{----`.
  | Hyphens -- sequence of two or more hyphens: `------`
  | InStringLit -- part of string literal
  | InLineComment -- part of line comment

commentSH : (k : Nat) -> CommentState -> Shifter False Char
commentSH 0       st sc cs = Res sc cs Same
commentSH n@(S k) st sc cs = case st of
  -- We are at an arbitrary position in a block comment
  -- of nesting level `n`.
  Block         => case cs of
    -- Start a new nesting of block comments.
    '{' :: '-' :: t => commentSH (S n) Opening (sc :< '{' :< '-') t ~?> sh2
    -- Close the current block comment, reducing the nesting level by one.
    '-' :: '}' :: t => commentSH k Block (sc :< '-' :< '}') t ~?> sh2
    -- Start a line comment or block closing sequence.
    '-' :: '-' :: t => commentSH n Hyphens (sc :< '-' :< '-') t ~?> sh2
    -- Start a string literal
    '"'        :: t => commentSH n InStringLit (sc :< '"') t ~?> sh1
    -- Continue in block
    h          :: t => commentSH n Block (sc :< h) t ~?> sh1
    []              => Res sc [] Same
  Opening       => case cs of
    -- Start a new nesting of block comments.
    '{' :: '-' :: t => commentSH (S n) Opening (sc :< '{' :< '-') t ~?> sh2
    -- Close the current block comment, reducing the nesting level by one.
    '-' :: '}' :: t => commentSH k Block (sc :< '-' :< '}') t ~?> sh2
    -- Add one more hyphen to the block opening sequence
    '-'        :: t => commentSH n Opening (sc :< '-') t ~?> sh1
    -- Start a string literal
    '"'        :: t => commentSH n InStringLit (sc :< '"') t ~?> sh1
    -- Continue in block
    h          :: t => commentSH n Block (sc :< h) t ~?> sh1
    []              => Res sc [] Same
  Hyphens     => case cs of
    -- Add one more hyphen to sequence.
    '-'  :: t => commentSH n Hyphens (sc :< '-') t ~?> sh1
    -- End of line: Abort line comment.
    '\n' :: t => commentSH n Block (sc :< '\n') t ~?> sh1
    -- Interpret hyphens as block closing sequence.
    '}'  :: t => commentSH k Block (sc :< '}') t ~?> sh1
    -- Interpret hyphens as line comment.
    h    :: t => commentSH n InLineComment (sc :< h) t ~?> sh1
    []        => Res sc [] Same
  InStringLit   => case cs of
    -- We can escape any character in a string literal.
    '\\' :: c :: t => commentSH n InStringLit (sc :< '\\' :< c) t ~?> sh2
    -- Close a string literal.
    '"'       :: t => commentSH n Block (sc :< '"') t ~?> sh1
    -- Continue in string literal.
    h         :: t => commentSH n InStringLit (sc :< h) t ~?> sh1
    -- We don't accept string literals that are not properly closed.
    []             => Stop
  InLineComment => case cs of
    -- Terminate line comment.
    '\n' :: t => commentSH n Block (sc :< '\n') t ~?> sh1
    -- Continue in line comment.
    h    :: t => commentSH n InLineComment (sc :< h) t ~?> sh1
    []        => Res sc [] Same

export
blockComment : Lexer
blockComment = Lift $ \sc,cs => case cs of
  '{' :: '-' :: t => commentSH 1 Opening (sc :< '{' :< '-') t ~> sh2
  _               => Stop

docComment : Lexer
docComment = exact "|||" <+> manyTillLineFeed

holeIdent : Lexer
holeIdent = is '?' <+> identNormal

dotIdent : Lexer
dotIdent = is '.' <+> identNormal

pragma : Lexer
pragma = is '%' <+> identNormal

doubleLit : Lexer
doubleLit = digits <+> is '.' <+> digits <+> opt (is 'e' <+> intLitPlus)

stringBegin : Lexer
stringBegin = many (is '#') <+> (is '"')

stringEnd : Nat -> String
stringEnd hashtag = "\"" ++ replicate hashtag '#'

multilineBegin : Lexer
multilineBegin =
  preds0 (== '#') <+> (exact "\"\"\"") <+> preds0 (== ' ') <+> newline

multilineEnd : Nat -> String
multilineEnd hashtag = "\"\"\"" ++ replicate hashtag '#'

-- Do this as an entire token, because the contents will be processed by
-- a specific back end
cgDirective : Lexer
cgDirective =
  exact "%cg" <+>
    ((spaceChars <+> preds isAlphaNum <+> preds0 (== ' ') <+>
        is '{' <+> preds (/= '}') <+> is '}') <|> preds0 (/= '\n'))

mkDirective : SnocList Char -> Token
mkDirective = CGDirective . pack . ltrim . dropHead 3 . rtrim

-- Reserved words
-- NB: if you add a new keyword, please add the corresponding documentation in
--     Idris.Doc.String
public export
keywords : List String
keywords = ["data", "module", "where", "let", "in", "do", "record",
            "auto", "default", "implicit", "failing", "mutual", "namespace",
            "parameters", "with", "proof", "impossible", "case", "of",
            "if", "then", "else", "forall", "rewrite",
            "using", "interface", "implementation", "open", "import",
            "public", "export", "private",
            "infixl", "infixr", "infix", "prefix",
            "total", "partial", "covering"]

public export
debugInfo : List DebugInfo
debugInfo = [ DebugLoc, DebugFile, DebugLine, DebugCol ]

-- Reserved words for internal syntax
special : List String
special = ["%lam", "%pi", "%imppi", "%let"]

public export
symbols : List String
symbols = [",", ";", "_", "`"]

export
groupSymbols : List String
groupSymbols = [".(", -- for things such as Foo.Bar.(+)
    ".[|", -- for namespaced brackets such as Foo.Bar.[| x + y |]
    "@{", "[|", "(", "{", "[<", "[>", "[", "`(", "`{", "`["]

export
groupClose : String -> String
groupClose ".(" = ")"
groupClose "@{" = "}"
groupClose "[|" = "|]"
groupClose ".[|" = "|]"
groupClose "(" = ")"
groupClose "[" = "]"
groupClose "[<" = "]"
groupClose "[>" = "]"
groupClose "{" = "}"
groupClose "`(" = ")"
groupClose "`{" = "}"
groupClose "`[" = "]"
groupClose _ = ""

validSymbol : Lexer
validSymbol = preds isOpChar

-- Valid symbols which have a special meaning so can't be operators
public export
reservedInfixSymbols : List String
reservedInfixSymbols
    = ["%", "\\", ":", "=", ":=", "$=", "|", "|||", "<-", "->", "=>", "?", "!",
       "&", "**", "..", "~", "@"]

-- Valid symbols which have a special meaning so can't be operators
public export
reservedSymbols : List String
reservedSymbols =
  symbols
    ++ groupSymbols ++ (groupClose <$> groupSymbols)
    ++ reservedInfixSymbols

fromBinLit : SnocList Char -> Integer
fromBinLit = go 1 0
  where
    go : (pow : Integer) -> (sum : Integer) -> SnocList Char -> Integer
    go pow sum (sc :< c) = case c of
      '_' => go pow sum  sc
      'b' => sum
      c   => go (2 * pow) (fromBinDigit c * 2 + sum) sc
    go pow sum [<] = sum

fromHexLit : SnocList Char -> Integer
fromHexLit = go 1 0
  where
    go : (pow : Integer) -> (sum : Integer) -> SnocList Char -> Integer
    go pow sum (sc :< c) = case c of
      '_' => go pow sum  sc
      'x' => sum
      c   => go (16 * pow) (fromHexDigit c * 16 + sum) sc
    go pow sum [<] = sum

fromOctLit : SnocList Char -> Integer
fromOctLit = go 1 0
  where
    go : (pow : Integer) -> (sum : Integer) -> SnocList Char -> Integer
    go pow sum (sc :< c) = case c of
      '_' => go pow sum  sc
      'o' => sum
      c   => go (8 * pow) (fromOctDigit c * 8 + sum) sc
    go pow sum [<] = sum

stringTokens : Bool -> Nat -> Tokenizer Char Token

rawTokens : Tokenizer Char Token

stringTokens multi hashtag =
  let escapeChars := "\\" ++ replicate hashtag '#'
      interpStart := escapeChars ++ "{"
      escapeLexer := escape (exact escapeChars) any
      charLexer   := non $ exact (if multi then multilineEnd hashtag else stringEnd hashtag)
   in Match (someUntil (exact interpStart) (escapeLexer <|> charLexer))
            (\x => StringLit hashtag $ pack x)
      <|> Compose (exact interpStart)
                  (const InterpBegin)
                  (const ())
                  (\_ => rawTokens)
                  (const $ is '}')
                  (const InterpEnd)

rawTokens =
      Match comment (const Comment)
  <|> Match blockComment (const Comment)
  <|> Match docComment (DocComment . pack . ltrim . dropHead 3)
  <|> Match cgDirective mkDirective
  <|> Match holeIdent (HoleIdent . pack . dropHead 1)
  <|> Compose (choice $ exact <$> groupSymbols)
              (Symbol . pack)
              id
              (\_ => rawTokens)
              (exact . groupClose . pack)
              (Symbol . pack)
  <|> choiceMap (\d => Match (exact "\{d}") (const $ MagicDebugInfo d)) debugInfo
  <|> Match (choice $ exact <$> symbols) (Symbol . pack)
  <|> Match doubleLit (DoubleLit . cast . pack)
  <|> Match binUnderscoredLit (IntegerLit . fromBinLit)
  <|> Match hexUnderscoredLit (IntegerLit . fromHexLit)
  <|> Match octUnderscoredLit (IntegerLit . fromOctLit)
  <|> Match digitsUnderscoredLit (IntegerLit . cast . pack)
  <|> Compose multilineBegin
              (const $ StringBegin Multi)
              countHashtag
              (stringTokens True)
              (exact . multilineEnd)
              (const StringEnd)
  <|> Compose stringBegin
              (const $ StringBegin Single)
              countHashtag
              (stringTokens False)
              (\hashtag => exact (stringEnd hashtag) <+> reject (is '"'))
              (const StringEnd)
  <|> Match charLit (CharLit . stripQuotes)
  <|> Match dotIdent (DotIdent . pack . dropHead 1)
  <|> Match namespacedIdent parseNamespace
  <|> Match identNormal (parseIdent . pack)
  <|> Match pragma (Pragma . pack . dropHead 1)
  <|> Match space (const Space)
  <|> Match validSymbol (Symbol . pack)
  <|> Match symbol (Unrecognised . pack)
  where
    parseIdent : String -> Token
    parseIdent x = if x `elem` keywords then Keyword x else Ident x

    parseNamespace : SnocList Char -> Token
    parseNamespace ns = case mkNamespacedIdent ns of
                             (Nothing, ident) => parseIdent ident
                             (Just ns, n)     => DotSepIdent ns n

export
lexTo : Lexer ->
        String ->
        Either (StopReason, Nat, Nat, String)
               ( List (WithBounds ())     -- bounds of comments
               , List (WithBounds Token)) -- tokens
lexTo reject str = case lexTo reject rawTokens str of
  TR l c ts EndInput cs _ =>
    -- Add the EndInput token so that we'll have a line and column
    -- number to read when storing spans in the file
    let end := [MkBounded EndInput (Just $ MkBounds l c l c)]
     in Right $ map (++ end)
              $ partitionEithers
              $ map spotComment
              $ filter isNotSpace
              $ ts <>> []
  TR l c _ r cs _ => Left (r, l, c, pack cs)
    where

      isNotSpace : WithBounds Token -> Bool
      isNotSpace t = case t.val of
        Space => False
        _ => True

      spotComment : WithBounds Token ->
                    Either (WithBounds ()) (WithBounds Token)
      spotComment t = case t.val of
        Comment => Left (() <$ t)
        _ => Right t

export %inline
lex :
     String
  -> Either (StopReason, Nat, Nat, String)
            ( List (WithBounds ())     -- bounds of comments
            , List (WithBounds Token)) -- tokens
lex = lexTo stop
