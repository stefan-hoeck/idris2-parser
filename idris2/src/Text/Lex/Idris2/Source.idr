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

public export
debugInfos : List DebugInfo
debugInfos = [DebugLoc, DebugFile, DebugLine, DebugCol]

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

commentSH : (k : Nat) -> CommentState -> AutoShift False Char
commentSH 0       st cs = Succ cs
commentSH n@(S k) st cs = case st of
  -- We are at an arbitrary position in a block comment
  -- of nesting level `n`.
  Block         => case cs of
    -- Start a new nesting of block comments.
    '{' :: '-' :: t => commentSH (S n) Opening t
    -- Close the current block comment, reducing the nesting level by one.
    '-' :: '}' :: t => commentSH k Block t
    -- Start a line comment or block closing sequence.
    '-' :: '-' :: t => commentSH n Hyphens t
    -- Start a string literal
    '"'        :: t => commentSH n InStringLit t
    -- Continue in block
    h          :: t => commentSH n Block t
    []              => Succ []
  Opening       => case cs of
    -- Start a new nesting of block comments.
    '{' :: '-' :: t => commentSH (S n) Opening t
    -- Close the current block comment, reducing the nesting level by one.
    '-' :: '}' :: t => commentSH k Block t
    -- Add one more hyphen to the block opening sequence
    '-'        :: t => commentSH n Opening t
    -- Start a string literal
    '"'        :: t => commentSH n InStringLit t
    -- Continue in block
    h          :: t => commentSH n Block t
    []              => Succ []
  Hyphens     => case cs of
    -- Add one more hyphen to sequence.
    '-'  :: t => commentSH n Hyphens t
    -- End of line: Abort line comment.
    '\n' :: t => commentSH n Block t
    -- Interpret hyphens as block closing sequence.
    '}'  :: t => commentSH k Block t
    -- Interpret hyphens as line comment.
    h    :: t => commentSH n InLineComment t
    []        => Succ []
  InStringLit   => case cs of
    -- We can escape any character in a string literal.
    '\\' :: c :: t => commentSH n InStringLit t
    -- Close a string literal.
    '"'       :: t => commentSH n Block t
    -- Continue in string literal.
    h         :: t => commentSH n InStringLit t
    -- We don't accept string literals that are not properly closed.
    []             => Stop
  InLineComment => case cs of
    -- Terminate line comment.
    '\n' :: t => commentSH n Block t
    -- Continue in line comment.
    h    :: t => commentSH n InLineComment t
    []        => Succ []

export
blockComment : Lexer
blockComment = Lift $ \sc,cs => case cs of
  '{' :: '-' :: t => commentSH 1 Opening {pre = sc :< '{' :< '-'} t
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

stringTokens : Bool -> Nat -> Tokenizer Token

rawTokens : Tokenizer Token

stringTokens multi hashtag =
  let escapeChars := "\\" ++ replicate hashtag '#'
      interpStart := escapeChars ++ "{"
      escapeLexer := escape (exact escapeChars) any
      charLexer   := non $ exact (if multi then multilineEnd hashtag else stringEnd hashtag)
   in Match [(someUntil (exact interpStart) (escapeLexer <|> charLexer),
            \x => StringLit hashtag $ pack x)]
      <|> Compose (exact interpStart)
                  (const InterpBegin)
                  (const ())
                  (\_ => rawTokens)
                  (const $ is '}')
                  (const InterpEnd)

rawTokens =
      Match
        [ (comment, const Comment)
        , (blockComment, const Comment)
        , (docComment, DocComment . pack . ltrim . dropHead 3)
        , (cgDirective, mkDirective)
        , (holeIdent, HoleIdent . pack . dropHead 1)
        , (choice $ map (exact . interpolate) debugInfos, parseIdent . pack)
        , (doubleLit, DoubleLit . cast . pack)
        , (binUnderscoredLit, IntegerLit . fromBinLit)
        , (hexUnderscoredLit, IntegerLit . fromHexLit)
        , (octUnderscoredLit, IntegerLit . fromOctLit)
        , (digitsUnderscoredLit, IntegerLit . cast . pack)
        ]
  <|> Compose (choice $ exact <$> groupSymbols)
              (Symbol . pack)
              id
              (\_ => rawTokens)
              (exact . groupClose . pack)
              (Symbol . pack)
  <|> Match [(choice $ exact <$> symbols, Symbol . pack)]
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
  <|> Match
        [ (charLit, CharLit . stripQuotes)
        , (dotIdent, DotIdent . pack . dropHead 1)
        , (namespacedIdent, parseNamespace)
        , (identNormal, parseIdent . pack)
        , (pragma, Pragma . pack . dropHead 1)
        , (space, const Space)
        , (validSymbol, Symbol . pack)
        , (symbol, Unrecognised . pack)
        ]
  where
    parseIdent : String -> Token
    parseIdent "__LOC__"  = MagicDebugInfo DebugLoc
    parseIdent "__FILE__" = MagicDebugInfo DebugFile
    parseIdent "__LINE__" = MagicDebugInfo DebugLine
    parseIdent "__COL__"  = MagicDebugInfo DebugCol
    parseIdent x = if x `elem` keywords then Keyword x else Ident x

    parseNamespace : SnocList Char -> Token
    parseNamespace ns = case mkNamespacedIdent ns of
                             (Nothing, ident) => parseIdent ident
                             (Just ns, n)     => DotSepIdent ns n

export
lexTo : Lexer ->
        String ->
        Either (StopReason, Nat, Nat, String)
               ( List (Bounded ())     -- bounds of comments
               , List (Bounded Token)) -- tokens
lexTo reject str = case lexTo reject rawTokens str of
  TR l c ts EndInput cs _ =>
    -- Add the EndInput token so that we'll have a line and column
    -- number to read when storing spans in the file
    let end := [BD EndInput (BS l c l c)]
     in Right $ map (++ end)
              $ partitionEithers
              $ map spotComment
              $ filter isNotSpace
              $ ts <>> []
  TR l c _ r cs _ => Left (r, l, c, pack cs)
    where

      isNotSpace : Bounded Token -> Bool
      isNotSpace t = case t.val of
        Space => False
        _ => True

      spotComment : Bounded Token ->
                    Either (Bounded ()) (Bounded Token)
      spotComment t = case t.val of
        Comment => Left (() <$ t)
        _ => Right t

export %inline
lex :
     String
  -> Either (StopReason, Nat, Nat, String)
            ( List (Bounded ())     -- bounds of comments
            , List (Bounded Token)) -- tokens
lex = lexTo stop
