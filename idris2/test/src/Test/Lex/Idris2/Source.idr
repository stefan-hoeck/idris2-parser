module Test.Lex.Idris2.Source

import Parser.Lexer.Source
import Libraries.Text.Lexer.Tokenizer
import Text.Lex.Idris2.Source
import Test.Lex.Idris2.Gen
import Test.Lex.Util

%default total

--------------------------------------------------------------------------------
--          Utilities
--------------------------------------------------------------------------------

0 PToken : Type
PToken = Idris2.Source.Token

0 IToken : Type
IToken = Lexer.Source.Token

0 PReason : Type
PReason = Lex.Tokenizer.StopReason

0 IReason : Type
IReason = Libraries.Text.Lexer.Tokenizer.StopReason

toML : Lexer.Source.IsMultiline -> Idris2.Source.IsMultiline
toML Multi  = Multi
toML Single = Single

toInfo : Lexer.Source.DebugInfo -> Idris2.Source.DebugInfo
toInfo DebugLoc = DebugLoc
toInfo DebugFile = DebugFile
toInfo DebugLine = DebugLine
toInfo DebugCol = DebugCol

toReason : Lexer.Tokenizer.StopReason -> Lex.Tokenizer.StopReason
toReason EndInput = EndInput
toReason NoRuleApply = NoRuleApply
toReason (ComposeNotClosing (a,b) (c,d)) =
  ComposeNotClosing (cast a, cast b) (cast c, cast d)

toToken : IToken -> PToken
toToken (CharLit str) = CharLit str
toToken (DoubleLit dbl) = DoubleLit dbl
toToken (IntegerLit i) = IntegerLit i
toToken (StringBegin x) = StringBegin (toML x)
toToken StringEnd = StringEnd
toToken InterpBegin = InterpBegin
toToken InterpEnd = InterpEnd
toToken (StringLit k str) = StringLit k str
toToken (HoleIdent str) = HoleIdent str
toToken (Ident str) = Ident str
toToken (DotSepIdent mi str) = DotSepIdent mi str
toToken (DotIdent str) = DotIdent str
toToken (Symbol str) = Symbol str
toToken Space = Space
toToken Comment = Comment
toToken (DocComment str) = DocComment str
toToken (CGDirective str) = CGDirective str
toToken EndInput = EndInput
toToken (Keyword str) = Keyword str
toToken (Pragma str) = Pragma str
toToken (MagicDebugInfo x) = MagicDebugInfo (toInfo x)
toToken (Unrecognised str) = Unrecognised str

toRes :
     Either (IReason, Int, Int, String) (List (IWithBounds ()), List (IWithBounds IToken))
  -> Either (PReason, Nat, Nat, String) (List (PWithBounds ()), List (PWithBounds PToken))
toRes (Left (r,c,l,s)) = Left (toReason r, cast c, cast l, s)
toRes (Right (bs,cs)) =
  Right (map toWithBounds bs, map (map toToken . toWithBounds) cs)

--------------------------------------------------------------------------------
--          Generators
--------------------------------------------------------------------------------

testLex : Monad m => String -> TestT m ()
testLex str =
  Lex.Idris2.Source.lex str === toRes (Lexer.Source.lex str)

prop_comment : Property
prop_comment = property $ forAll comment >>= testLex

prop_keyword : Property
prop_keyword = property $ forAll sourceKeyword >>= testLex

prop_debugInfo : Property
prop_debugInfo = property $ forAll debugInfo >>= testLex

prop_docComment : Property
prop_docComment = property $ forAll docComment >>= testLex

prop_blockComment : Property
prop_blockComment = property $ forAll blockComment >>= testLex

prop_cgDirective : Property
prop_cgDirective = property $ forAll cgDirective >>= testLex

prop_hole : Property
prop_hole = property $ forAll hole >>= testLex

prop_dotIdent : Property
prop_dotIdent = property $ forAll dotIdent >>= testLex

prop_pragma : Property
prop_pragma = property $ forAll pragma >>= testLex

prop_source : Property
prop_source = withTests 1 $ property $ testLex src

export
props : Group
props = MkGroup "Lex.Idris2.Package" [
    ("prop_comment", prop_comment)
  , ("prop_keyword", prop_keyword)
  , ("prop_debugInfo", prop_debugInfo)
  , ("prop_docComment", prop_docComment)
  , ("prop_blockComment", prop_blockComment)
  , ("prop_cgDirective", prop_cgDirective)
  , ("prop_hole", prop_hole)
  , ("prop_dotIdent", prop_dotIdent)
  , ("prop_pragma", prop_pragma)
  , ("prop_source", prop_source)
  ]
