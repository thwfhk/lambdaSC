{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use <&>" #-}
{-# HLINT ignore "Use <$>" #-}
module Parser where

import Debug.Trace

import Text.Parsec
import Text.Parsec.Char (digit)
import Control.Monad.Except

import qualified Text.Parsec.Expr as Ex
import qualified Text.Parsec.Token as Tok

import Data.List
import Data.Functor.Identity (Identity)
import Control.Applicative (empty)

import Lexer
import Syntax
import Context
import Evaluation (shiftC, shiftV)


type Parser a = ParsecT String Context (Except Err) a

sourcePos :: Monad m => ParsecT s u m SourcePos
sourcePos = statePos `liftM` getParserState

----------------------------------------------------------------
-- * Command Parser

parseCmds :: Parser [Command]
parseCmds = do
    ctx <- getState
    cmds <- many (parseDef <|> parseRun)
    setState ctx
    return cmds

parseDef :: Parser Command
parseDef = do
  reserved "DEF"
  x <- identifier
  reservedOp "="
  v <- parseValue
  ctx <- getState
  setState $ addBinding ctx (x, NameBind)
  return $ Def x v

parseRun :: Parser Command
parseRun = do
  reserved "RUN"
  c <- parseComp
  return $ Run c
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
  , parseOpened
  , parseClosed
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
  pos <- sourcePos
  case name2index ctx var pos of -- the only use of context during parsing
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

parseOpened :: Parser Value
parseOpened = reserved "opened" >> parseValue >>= return . Vret

parseClosed :: Parser Value
parseClosed = reserved "closed" >> parseValue >>= return . Vret

----------------------------------------------------------------
-- * Computation Parser

parseComp :: Parser Comp
parseComp = (whiteSpace >>) . choice $
  [ parseRet
  , parseLet
  , parseOp
  , parseSc
  , parseDo
  , parseIf
  , parseCase
  ]
  ++ map getFunc1Parser builtInFunc1
  ++ map getFunc2Parser builtInFunc2
  ++
  [ try parseHandle
  , try parseApp' -- I guess App should be the last one
  , parens parseComp
  ]

parseRet :: Parser Comp
parseRet = reserved "return" >> parseValue >>= return . Return

parseApp :: Parser Comp
parseApp = do
  v1 <- parseValue
  v2 <- parseValue
  return $ App v1 v2

parseApp' :: Parser Comp
parseApp' = do
  v <- parseValue
  vs <- many1 parseValue
  -- return $ App' (v:vs)
  return $ apps2app v vs -- desugar
  where
    apps2app :: Value -> [Value] -> Comp
    apps2app f []     = error "apps2app: [] is impossible"
    apps2app f [v]    = App f v
    apps2app f (v:vs) = Do "f" (App f v) (apps2app (Var "f" 0) $ map (shiftV 1) vs)


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
  try (parens ( do y <- identifier
                   dot
                   ctx <- getState
                   setState $ addBinding ctx (y, NameBind)
                   c <- parseComp
                   setState ctx
                   return $ Op l v (y :. c)
              )) <|> return (Op l v ("y" :. Return (Var "y" 0)))

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
  (z, c2) <- try (parens ( do z <- identifier
                              dot
                              ctx <- getState
                              setState $ addBinding ctx (z, NameBind)
                              c <- parseComp
                              setState ctx
                              return (z, c)
                         )) <|> return ("z", Return (Var "z" 0))
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

parseCase :: Parser Comp
parseCase = do
  reserved "case"
  v <- parseValue
  reserved "of"
  reserved "left"
  x <- identifier
  reserved "->"
  ctx <- getState
  setState $ addBinding ctx (x, NameBind)
  c1 <- parseComp
  setState ctx
  reserved "right"
  y <- identifier
  reserved "->"
  ctx <- getState
  setState $ addBinding ctx (y, NameBind)
  c2 <- parseComp
  setState ctx
  return $ Case v x c1 y c2


-- TODO: a lot of other computations

getFunc1Parser :: (String, Value -> Comp) -> Parser Comp
getFunc1Parser (name, cons) = reserved name >> parseValue >>= return . cons

getFunc2Parser (name, cons, b) = if b
  then try $ do v1 <- parseValue; reservedOp name; v2 <- parseValue; return $ cons v1 v2
  else do reserved name; v1 <- parseValue; v2 <- parseValue; return $ cons v1 v2

-- ad-hoc parsers for the parser example
parseOr :: Parser Comp
parseOr = try $ do
  c1 <- parseComp;
  reservedOp "<>";
  c2 <- parseComp;
  return $ cor c1 c2

parseMany1 :: Parser Comp
parseMany1 = do
  reserved "many1"
  v <- parseValue
  return $ cmany1 v

cmany1 :: Value -> Comp
cmany1 p = Do "a" (App p Vunit) $
           Do "as" (cor (cmany1 p) (Return (Vstr ""))) $
           Do "x" (ConsS (Var "a" 1) (Var "as" 0)) $
           Return (Var "x" 0)

cor :: Comp -> Comp -> Comp
cor x y = Op "choose" Vunit ("b" :. If (Var "b" 0) (shiftC 1 x) (shiftC 1 y))

----------------------------------------------------------------
-- * Handler Parser

parseHandler :: Parser Handler
parseHandler = do
    reserved "handler"
    tyopt <- brackets parseTypeOpt
    cls <- parseClauses
    clauses2handler cls tyopt
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

----------------------------------------------------------------
-- * Type Parser

parseTypeOpt :: Parser TypeOpt
-- parseTypeOpt = do
--   reservedOp "\\"
--   x <- identifier
--   dot
--   reserved "List"
--   _ <- identifier
--   return (TAbs x (TList (TVar x)))
  -- TODO: temporarily fix the shape to \ x . List x
parseTypeOpt =
  (do
    reservedOp "\\"
    x <- identifier
    reservedOp ":"
    k <- parseKind
    dot
    t <- parseTypeOpt
    return $ TAbs x k t)
  <|>
  (do
    t <- parseVType
    return $ TNil t)

parseKind :: Parser Kind
parseKind =
      (reservedOp "*" >> return ValueType)
  <|> (reserved "Eff" >> return EffectType)

parseVType :: Parser VType
parseVType = (whiteSpace >>) $ choice
  [ try parseTVar
  , parseTUnit
  , parseTInt
  , parseTBool
  , parseTEmpty
  , parseTString
  , parseTPair
  , parseTList
  , try parseTSum
  , try parseArr -- should be the last one
  ]

-- NOTE: I didn't use De Bruijn index for types.
-- So be careful about alpha renaming.

parseTVar :: Parser VType
parseTVar = do
  var <- identifier
  return $ TVar var

parseTUnit :: Parser VType
parseTUnit = reserved "Unit" >> return TUnit

parseTInt :: Parser VType
parseTInt = reserved "Int" >> return TInt

parseTBool :: Parser VType
parseTBool = reserved "Bool" >> return TBool

parseTString :: Parser VType
parseTString = reserved "String" >> return TString

parseTEmpty :: Parser VType
parseTEmpty = reserved "Empty" >> return TEmpty

parseTPair :: Parser VType
parseTPair = parens $ do
  t1 <- parseVType
  comma
  t2 <- parseVType
  return $ TPair t1 t2

parseTSum :: Parser VType
parseTSum = do
  reserved "Sum"
  t1 <- parseVType
  t2 <- parseVType
  return $ TSum t1 t2

parseArr :: Parser VType
parseArr = do
  reserved "Arr"
  vt <- parseVType
  -- reservedOp "->"
  ct <- parseCType
  return $ TArr vt ct

parseTList :: Parser VType
parseTList = do
  reserved "List"
  t <- parseVType
  return $ TList t

-- binary :: String -> (a -> a -> a) -> Ex.Assoc -> Ex.Operator String u (Except Err) a
-- binary s f = Ex.Infix (reservedOp s >> return f)


-- typeOps :: [[Ex.Operator String u (Except Err) VType]]
-- typeOps = [ [ binary "->" TArr Ex.AssocRight] ]

-- parseVType :: Parser VType
-- parseVType = whiteSpace >> Ex.buildExpressionParser typeOps parsePrimVType


parseCType :: Parser CType
parseCType = do
  vt <- parseVType
  reservedOp "!"
  et <- parseEType
  return $ vt <!> et
  <|> parens parseCType

parseEType :: Parser EType
parseEType = parseEVar
-- parseEType = do
--   reservedOp "<"
--   ls <- semiSep identifier
--   (do reservedOp ">"
--       return (foldl (flip ECons) EEmpty ls)
--    ) <|> (do reservedOp ";"
--              mu <- parseEVar
--              reservedOp ">"
--              return (foldl (flip ECons) mu ls)
--    )

-- parseEEmpty :: Parser EType
-- parseEEmpty = reservedOp "<" >> whiteSpace >> reservedOp ">" >> return EEmpty

parseEVar :: Parser EType
parseEVar = do
  var <- identifier
  return $ EVar var