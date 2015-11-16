module Conway

import Data.Vect

-- Local Variables:
-- idris-load-packages: ("prelude" "effects" "contrib" "base")
-- End:

board : Nat -> Nat -> Type
board n m = Vect n (Vect m Bool)

printChar : Bool -> String
printChar False = "x"
printChar True = "o"

printRow : Vect m Bool -> String
printRow [] = "\n"
printRow (x :: xs) = (printChar x) ++ (printRow xs)

printBoard : board n m -> String
printBoard = concat . map printRow 

listFins : (n : Nat) -> Vect n (Fin n)
listFins Z = []
listFins (S k) = FZ :: (map FS (listFins k))

boardAux : Fin n -> Vect m (Fin n, Fin m)
boardAux {n} {m} f = map (\x => (f,x)) (listFins m) 

boardCoords : (n : Nat) -> (m : Nat) -> Vect n (Vect m (Fin n, Fin m))
boardCoords n m = map boardAux (listFins n)

rhs : (b : Vect n (Vect m Bool)) -> (Fin n, Fin m) -> Bool
rhs b f = ?blah

promote : Fin k ->  Fin (S k)
promote FZ = FZ
promote (FS x) = (FS (promote x))

safeDec : Fin n -> Fin n
safeDec FZ = FZ
safeDec (FS x) = promote x

-- this should return the maximum element in the finite set
safeInc : Fin n -> Fin n
safeInc f = ?saferhs

filterV : (a -> Bool) -> Vect n a -> (m ** (Vect m a))
filterV f [] = (0 ** [])
filterV f (x :: xs) = case (f x) of
                       True => let (n ** xs') = filterV f xs in (S n ** (x :: xs'))
                       False => filterV f xs

nubV : Eq a => Vect n a -> (m ** (Vect m a))
nubV [] = (Z ** [])
nubV (x :: xs) = let (n ** xs') = filterV (\y => y /= x) xs 
                     (n' ** xs'') = nubV xs'
                 in (S n' ** (x :: xs''))

gameStep : board n m -> board n m
gameStep {n} {m} b = let coords = boardCoords n m in map (map (rhs b)) coords 
