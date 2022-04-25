module Parser where

import Debug.Trace

import Text.Parsec
import Text.Parsec.Char (digit)
import Control.Monad.Except

import qualified Text.Parsec.Expr as Ex
import qualified Text.Parsec.Token as Tok

import Data.Functor.Identity (Identity)
import Control.Applicative (empty)

import Lexer
import Syntax
import Context


type Parser a = ParsecT String Context (Except Err) a

----------------------------------------------------------------
-- * Value Parser

parseValue :: Parser Value
parseValue = (whiteSpace >>) $ choice
  [ try parseVar
  , parseLam
  , unit
  , true
  , false
  , int
  , parseChar
  , parseString
  , try parsePair
  , parseSum
  , parseList
  , try parseVHandler
  , parens parseValue
  ]

parseVar :: Parser Value
parseVar = do
  var <- identifier
  ctx <- getState
  case name2index ctx var of -- the only use of context during parsing
    Right idx -> return $ Var var idx
    Left e -> throwError e

parseLam :: Parser Value
parseLam = do
  reservedOp "\\"
  x <- identifier
  dot
  ctx <- getState
  setState $ addBinding ctx (x, NameBind)
  c <- parseComp
  setState ctx
  return $ Lam x c

unit :: Parser Value
unit = reserved "unit" >> return Vunit

parsePair :: Parser Value
parsePair = parens $ do
  v1 <- parseValue
  comma
  v2 <- parseValue
  return $ Vpair (v1, v2)

parseVHandler :: Parser Value
parseVHandler = parseHandler >>= return . Vhandler

true :: Parser Value
true = reserved "true" >> return (Vbool True)

false :: Parser Value
false = reserved "false" >> return (Vbool False)

int :: Parser Value
int = integer >>= return . Vint . fromIntegral

parseChar :: Parser Value
parseChar = charLiteral >>= return . Vchar

parseString :: Parser Value
parseString = stringLiteral >>= return . Vstr

parseList :: Parser Value
parseList = brackets $ commaSep parseValue >>= return . Vlist

parseSum :: Parser Value
parseSum  =  (reserved "left" >> parseValue >>= return . Vsum . Left)
         <|> (reserved "right" >> parseValue >>= return . Vsum . Right)

-- TODO: parseCutlist

-- TODO: parseMem

----------------------------------------------------------------
-- * Computation Parser

parseComp :: Parser Comp
parseComp = (whiteSpace >>) $ choice
  [ parseRet
  , parseLet
  , parseOp
  , parseSc
  , parseDo
  , parseIf
  , try parseApp
  , try parseHandle
  , parens parseComp
  ]

parseRet :: Parser Comp
parseRet = reserved "return" >> parseValue >>= return . Return

-- is it ok?
parseApp :: Parser Comp
parseApp = do
  v1 <- parseValue
  v2 <- parseValue
  return $ App v1 v2

parseHandle :: Parser Comp
parseHandle = do
  h <- parseValue
  reservedOp "#"
  c <- parseComp
  return $ Handle h c

parseLet :: Parser Comp
parseLet = do
  reserved "let"
  x <- identifier
  reservedOp "="
  v <- parseValue
  reserved "in"
  ctx <- getState
  setState $ addBinding ctx (x, NameBind)
  c <- parseComp
  setState ctx
  return $ Let x v c

parseOp :: Parser Comp
parseOp = do
  reserved "op"
  l <- identifier
  v <- parseValue
  parens $ do y <- identifier
              dot
              ctx <- getState
              setState $ addBinding ctx (y, NameBind)
              c <- parseComp
              setState ctx
              return $ Op l v (y :. c)

parseSc :: Parser Comp
parseSc = do
  reserved "sc"
  l <- identifier
  v <- parseValue
  (y, c1) <- parens $ do y <- identifier
                         dot
                         ctx <- getState
                         setState $ addBinding ctx (y, NameBind)
                         c <- parseComp
                         setState ctx
                         return (y, c)
  (z, c2) <- parens $ do z <- identifier
                         dot
                         ctx <- getState
                         setState $ addBinding ctx (z, NameBind)
                         c <- parseComp
                         setState ctx
                         return (z, c)
  return $ Sc l v (y :. c1) (z :. c2)

parseDo :: Parser Comp
parseDo = do
  reserved "do"
  x <- identifier
  reservedOp "<-"
  c1 <- parseComp
  semi
  ctx <- getState
  setState $ addBinding ctx (x, NameBind)
  c2 <- parseComp
  setState ctx
  return $ Do x c1 c2

parseIf :: Parser Comp
parseIf = do
  reserved "if"
  v <- parseValue
  whiteSpace -- interesting
  reserved "then"
  c1 <- parseComp
  whiteSpace
  reserved "else"
  c2 <- parseComp
  return $ If v c1 c2

-- TODO: a lot of other computations



-- binary :: String -> (a -> a -> a) -> Ex.Assoc -> Ex.Operator String u (Except Err) a
-- binary s f assoc = Ex.Infix (reservedOp s >> return f) assoc

-- compOps :: [[Ex.Operator String u (Except Err) Comp]]
-- compOps = [ [ binary "+" Add Ex.AssocLeft ] ]

-- parseType :: Parser Comp
-- parseType = whiteSpace >> Ex.buildExpressionParser typeOps parsePrimType

-- parseTerm :: Parser Comp
-- parseTerm = whiteSpace >> chainl1 (try parsePrimComp) (return App)


----------------------------------------------------------------
-- * Handler Parser

parseHandler :: Parser Handler
parseHandler = do
    reserved "handler"
    cls <- parseClauses
    h <- clauses2handler cls
    return h
  <|> parens parseHandler

parseClauses :: Parser [Clause]
parseClauses = braces $ commaSep parseClause

parseClause :: Parser Clause
parseClause  =  parseRetClause
            <|> parseOpClause
            <|> parseScClause
            <|> parseFwdClause

parseRetClause :: Parser Clause
parseRetClause = do
  reserved "return"
  x <- identifier
  reservedOp "|->"
  ctx <- getState
  setState $ addBinding ctx (x, NameBind)
  c <- parseComp
  setState ctx
  return $ RetClause x c

parseOpClause :: Parser Clause
parseOpClause = do
  reserved "op"
  l <- identifier
  x <- identifier
  k <- identifier
  reservedOp "|->"
  ctx <- getState
  setState $ addBindings ctx [(x, NameBind), (k, NameBind)]
  c <- parseComp
  setState ctx
  return $ OpClause l x k c

parseScClause :: Parser Clause
parseScClause = do
  reserved "sc"
  l <- identifier
  x <- identifier
  p <- identifier
  k <- identifier
  reservedOp "|->"
  ctx <- getState
  setState $ addBindings ctx [(x, NameBind), (p, NameBind), (k, NameBind)]
  c <- parseComp
  setState ctx
  return $ ScClause l x p k c

parseFwdClause :: Parser Clause
parseFwdClause = do
  reserved "fwd"
  f <- identifier
  p <- identifier
  k <- identifier
  reservedOp "|->"
  ctx <- getState
  setState $ addBindings ctx [(f, NameBind), (p, NameBind), (k, NameBind)]
  c <- parseComp
  setState ctx
  return $ FwdClause f p k c
