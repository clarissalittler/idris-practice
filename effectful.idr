import Effects
import Effect.StdIO
import Effect.State

-- Local Variables:
-- idris-load-packages: ("contrib" "prelude" "effects" "base")
-- End:

-- this is mostly code from the tutorial on effects
hello : Eff () [STDIO]
hello = putStrLn "hello world!"


data BTree a = Leaf
             | Node (BTree a) a (BTree a)

testTree : BTree String
testTree = Node (Node Leaf "Jim" Leaf)
                "Fred"
                (Node (Node Leaf "Alice" Leaf)
                      "Sheila"
                      (Node Leaf "Bob" Leaf))


treeTagAux : BTree a -> Eff (BTree (Int,a)) [STATE Int]
treeTagAux Leaf = pure Leaf
treeTagAux (Node b1 x b2) = do
                    b1' <- treeTagAux b1
                    i <- get
                    put (i + 1)
                    b2' <- treeTagAux b2
                    pure (Node b1' (i,x) b2')

-- So one of the things that I find super fascinating are the dependent effects
-- obviously such things are needed for the purpose of having things like state that
-- contain dependent types, but it's also just really neat and makes, at least to me,
-- more sense than the simple-type-theory style monadic approach to semantics
-- The way I think I see effects in Idris is that you're essentially creating an internal
-- language of an effect and then you need to give a semantics of the effect in terms of
-- the types that support the operation and *that* is what the handlers are. 

-- Let's try making a reader effect, one that has an ask and local operation

data Reader : Effect where
  Ask : Reader a a (\x => a)
  Local : (a -> b) -> Reader c b f -> Reader c a (\x => a)
  
-- I think that's the right signature, it type checks at least. It's a little more complicated
-- than a normal reader because there could be some kind of dependent type in the reader state
-- such as, I don't know, an environment that's indexed by its length?

-- so what we're trying to do here is 
-- run the "local" effect with the resource (f r)
-- get back the value, in this case of type 't' from the local effect action
-- then restore the original state by passing that to the original continuation
-- now where I'm getting stuck, I think, is that, to me, this should clearly be something
-- kinda like
--  handle (f r) loc (\t _ => k t r)

 rhs : (m : Type -> Type) -> (r : res) -> (act : Reader t res resk) -> (k : (x : t) -> resk x -> m a) -> m a
 rhs m r Ask k = k r r
 rhs m r (Local f loc) k = rhs m (f r) loc (\ t,_ => k t r) -- Why did this work but recursion in handle didn't???

 READER : Type -> EFFECT
 READER t = MkEff t Reader -- yeah this part is just like state aren't I clever 

instance Handler Reader m where
  handle r act k = rhs m r act k

{- 
instance Handler Reader m where
  handle r Ask k = k r r
  handle r (Local f loc) k = handle (f r) loc ?f
-}
