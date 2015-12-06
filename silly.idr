%include JavaScript "silly.js"

jscall : (fname : String) -> (ty : Type) ->
          {auto fty : FTy FFI_JS [] ty} -> ty
jscall fname ty = foreign FFI_JS fname ty 

-- I don't know what I'm supposed to import to make this work given that the documentation shows this jscall function like it's a given so ???
-- and then when I add this function it looks like some of the other types aren't defined. 
-- so what exactly from the documentation already exists and what do you just have to copy over?
counterMaker : JS_IO (() -> JS_IO Int)
counterMaker = jscall "counterMaker" (JS_IO (Js_Fn ( () -> JS_IO Int)))

main : JS_IO ()
main = do
  c <- counterMaker
  i <- jscall "%0()" (Js_Fn ( () -> JS_IO Int) -> JS_IO Int) c
  print i
