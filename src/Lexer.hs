module Lexer where

import Text.Parsec hiding (Parsec)
import Text.Parsec.Language hiding (emptyDef)

import qualified Text.Parsec.Token as Tok

import Data.Functor.Identity ( Identity )
import Control.Monad.Except

import Syntax

emptyDef :: GenLanguageDef String st (Except Err)
emptyDef = Tok.LanguageDef
    { Tok.commentStart   = ""
    , Tok.commentEnd     = ""
    , Tok.commentLine    = ""
    , Tok.nestedComments = True
    , Tok.identStart     = letter <|> char '_'
    , Tok.identLetter    = alphaNum <|> oneOf "_'"
    , Tok.opStart        = Tok.opLetter emptyDef
    , Tok.opLetter       = oneOf ":!#$%&*+./<=>?@\\^|-~"
    , Tok.reservedOpNames= []
    , Tok.reservedNames  = []
    , Tok.caseSensitive  = True
    }

langDef :: Tok.GenLanguageDef String st (Except Err)
langDef = emptyDef
    { Tok.commentLine = "--"
    , Tok.reservedOpNames = ops
    , Tok.reservedNames = names
    }
  where
    ops = [ "\\" -- lambda
          , "="
          , "<-"
          , "#" -- star
          , "|->"
          , "+"
          , "-"
          , "*"
          , "++"
          , "=="
          , ">"
          , "->"
          , "<>"
          , "<"
          ]
    names = [ "unit"
            , "true"
            , "false"
            , "left"
            , "right"
            , "if"
            , "then"
            , "else"
            , "return"
            , "let"
            , "in"
            , "op"
            , "sc"
            , "do"
            , "handler"
            , "DEF"
            , "RUN"
            ---------------
            , "head"
            , "tail"
            , "concatMap"
            , "concatMapCutList"
            , "append"
            , "open"
            , "close"
            , "opened"
            , "closed"
            , "fst"
            , "snd"
            , "absurd"
            , "case"
            , "of"
            , "read"
            , "many1"
            ---------------
            , "List"
            , "Unit"
            , "Int"
            , "Bool"
            , "String"
            , "Empty"
            , "Sum"
            ]

lexer :: Tok.GenTokenParser String u (Except Err)
-- lexer :: Tok.GenTokenParser String u Identity
lexer = Tok.makeTokenParser langDef

type Parsec s u a = ParsecT s u (Except Err) a

comma :: Parsec String u String
comma = Tok.comma lexer

dot :: Parsec String u String
dot = Tok.dot lexer

colon :: Parsec String u String
colon = Tok.colon lexer

semi :: Parsec String u String
semi = Tok.semi lexer

parens :: Parsec String u a -> Parsec String u a
parens = Tok.parens lexer

brackets :: Parsec String u a -> Parsec String u a
brackets = Tok.brackets lexer

braces :: Parsec String u a -> Parsec String u a
braces = Tok.braces lexer

integer :: Parsec String u Integer
integer = Tok.integer lexer

charLiteral :: Parsec String u Char
charLiteral = Tok.charLiteral lexer

stringLiteral :: Parsec String u String
stringLiteral = Tok.stringLiteral lexer

whiteSpace :: Parsec String u ()
whiteSpace = Tok.whiteSpace lexer

commaSep :: Parsec String u a -> Parsec String u [a]
commaSep = Tok.commaSep lexer

semiSep :: Parsec String u a -> Parsec String u [a]
semiSep = Tok.semiSep lexer

identifier :: Parsec String u String
identifier = Tok.identifier lexer

reserved :: String -> Parsec String u ()
reserved = Tok.reserved lexer

reservedOp :: String -> Parsec String u ()
reservedOp = Tok.reservedOp lexer