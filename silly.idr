%include JavaScript "silly.js"


-- I don't know what I'm supposed to import to make this work given that the documentation shows this jscall function like it's a given so ???
counterMaker : JS_IO (() -> JS_IO Int)
counterMaker = jscall "counterMaker" (JS_IO (Js_Fn ( () -> JS_IO Int)))

main : JS_IO ()
main = do
  c <- counterMaker
  i <- jscall "%0()" (Js_Fn ( () -> JS_IO Int) -> JS_IO Int) c
  print i
