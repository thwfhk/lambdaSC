import System.Environment
import WebAPI
import Run
import CodeString

f :: String -> String
f = interpret

main :: IO ()
main = do
  editor <- getElementById "editor"
  output <- getElementById "output"
  runButton <- getElementById "run"

  addEventListener runButton "click" (\_ -> do
    v <- value editor
    innerHTML output (f v))

  button <- getElementById "intro"
  addEventListener button "click" (\_ -> do
    setValue editor intro)

  button <- getElementById "once"
  addEventListener button "click" (\_ -> do
    setValue editor once)

  button <- getElementById "cut"
  addEventListener button "click" (\_ -> do
    setValue editor cut)

  button <- getElementById "catch"
  addEventListener button "click" (\_ -> do
    setValue editor catch)

  button <- getElementById "local"
  addEventListener button "click" (\_ -> do
    setValue editor local)

  button <- getElementById "depth"
  addEventListener button "click" (\_ -> do
    setValue editor depth)

  button <- getElementById "parser"
  addEventListener button "click" (\_ -> do
    setValue editor parser)