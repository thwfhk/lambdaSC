import System.Environment
import WebAPI
import Run
import CodeString

f :: String -> String
f = interpret

main :: IO ()
main = do
  body <- docBody
  title <- createElement "h1"
  t <- createTextNode "Online LambdaSC Interpreter"
  appendChild title t

  input <- createElement "textarea"
  setAttribute input "rows" "30"
  setAttribute input "cols" "80"
  -- exampleOnce <- readFile "exampleCodes/once.sc"
  -- test <- readFile "exampleCode/test.sc"
  t <- createTextNode exampleOnce
  appendChild input t

  button <- createElement "button"
  textButton <- createTextNode "Run"
  appendChild button textButton
  setAttribute button "style" "height:50px;width:50px"
  output <- createElement "pre"
  addEventListener button "click" (\_ -> do
    v <- value input
    innerHTML output (f v))

  button1 <- createElement "button"
  t <- createTextNode "inc example"
  appendChild button1 t
  addEventListener button1 "click" (\_ -> do
    setValue input exampleInc)

  button2 <- createElement "button"
  t <- createTextNode "once example"
  appendChild button2 t
  addEventListener button2 "click" (\_ -> do
    setValue input exampleOnce)

  br <- createElement "br"

  appendChild body title
  appendChild body button1
  appendChild body button2
  appendChild body br
  appendChild body input
  appendChild body br
  appendChild body button
  appendChild body output