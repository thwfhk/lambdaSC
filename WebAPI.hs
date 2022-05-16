{-# LANGUAGE InterruptibleFFI #-}

module WebAPI
  ( consoleLog,
    createElement,
    setAttribute,
    appendChild,
    setHidden,
    addEventListener,
    createTextNode,
    replaceWith,
    randomString,
    getElementById,
    docBody,
    showStr,
    innerHTML,
    value,
    setValue
  )
where

import Asterius.ByteString
import Asterius.Types
import Control.Exception
import qualified Data.ByteString as BS
import Data.ByteString.Unsafe
import Data.Coerce
import Foreign.Ptr

createElement :: String -> IO JSVal
createElement = js_createElement . toJSString

setAttribute :: JSVal -> String -> String -> IO ()
setAttribute e k v = js_setAttribute e (toJSString k) (toJSString v)

addEventListener :: JSVal -> String -> (JSObject -> IO ()) -> IO ()
addEventListener target event handler = do
  callback <- makeHaskellCallback1 handler
  js_addEventListener target (toJSString event) callback

createTextNode :: String -> IO JSVal
createTextNode = js_createTextNode . toJSString

randomString :: IO String
randomString = fromJSString <$> js_randomString

getElementById :: String -> IO JSVal
getElementById k = js_getElementById (toJSString k)

showStr :: String -> IO ()
showStr = js_showStr . toJSString

innerHTML :: JSVal -> String -> IO ()
innerHTML p s = js_innerHTML p (toJSString s)

setValue :: JSVal -> String -> IO ()
setValue p s = js_setvalue p (toJSString s)

value :: JSVal -> IO String
value x = js_value x >>= return . fromJSString

foreign import javascript "document.body"
  docBody :: IO JSVal

foreign import javascript "console.log($1)" consoleLog :: JSVal -> IO ()

foreign import javascript "document.createElement($1)"
  js_createElement :: JSString -> IO JSVal

foreign import javascript "$1.setAttribute($2,$3)"
  js_setAttribute :: JSVal -> JSString -> JSString -> IO ()

foreign import javascript "$1.appendChild($2)"
  appendChild :: JSVal -> JSVal -> IO ()

foreign import javascript "$1.hidden = $2"
  setHidden :: JSVal -> Bool -> IO ()

foreign import javascript "$1.addEventListener($2,$3)"
  js_addEventListener :: JSVal -> JSString -> JSFunction -> IO ()

foreign import javascript "document.createTextNode($1)"
  js_createTextNode :: JSString -> IO JSVal

foreign import javascript "$1.replaceWith($2)"
  replaceWith :: JSVal -> JSVal -> IO ()

foreign import javascript "Math.random().toString(36).slice(2)"
  js_randomString :: IO JSString

foreign import javascript "document.getElementById($1)"
  js_getElementById :: JSString -> IO JSVal

foreign import javascript "wrapper"
  makeHaskellCallback1 :: (JSObject -> IO ()) -> IO JSFunction

foreign import javascript
   "(() => {                                    \
   \   var d = document.createElement('p'); \
   \   d.innerHTML = $1;                      \
   \   document.body.appendChild(d);            \
   \ })()"
   js_showStr :: JSString -> IO ()

foreign import javascript "$1.innerHTML = $2"
   js_innerHTML :: JSVal -> JSString -> IO ()

foreign import javascript "$1.value"
   js_value :: JSVal -> IO JSString

foreign import javascript "$1.value = $2"
   js_setvalue :: JSVal -> JSString -> IO ()