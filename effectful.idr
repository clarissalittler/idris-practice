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
