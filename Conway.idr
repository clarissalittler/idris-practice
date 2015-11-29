module Conway

import Data.Vect
import Data.Fin

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

promote : Fin k ->  Fin (S k)
promote FZ = FZ
promote (FS x) = (FS (promote x))

safeDec : Fin n -> Fin n
safeDec FZ = FZ
safeDec (FS x) = promote x

maxFin : (n : Nat) -> Fin (S n) 
maxFin Z = FZ
maxFin (S k) = FS (maxFin k)

-- this should return the maximum element in the finite set
safeInc : Fin n -> Fin n
safeInc {n = Z} FZ impossible
safeInc {n = Z} (FS _) impossible
safeInc {n = (S k)} f = case (strengthen f) of
                          Left same => same
                          Right f' => (FS f')

myStrengthen : Fin (S n) -> Either (Fin (S n)) (Fin n)
myStrengthen {n = Z} f = Left FZ
myStrengthen {n = (S k)} FZ = Right FZ
myStrengthen {n = (S k)} (FS x) = case (myStrengthen x) of
                                   Left same => Left (FS x)
                                   Right decked => Right (FS decked)

lastV : Vect (S n) a -> a
lastV (x :: []) = x
lastV (x :: (y :: xs)) = lastV (y :: xs)

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

neighCoords : Fin n -> Fin m -> List (Fin n, Fin m)
neighCoords fx fy = [(safeInc fx , fy),
                     (safeInc fx , safeInc fy),
                     (fx , safeInc fy),
                     (safeDec fx, safeInc fy),
                     (safeInc fx , safeDec fy),
                     (safeDec fx, fy),
                     (fx , safeDec fy),
                     (safeDec fx, safeDec fy)]
                     
ixer : board n m -> (Fin n, Fin m) -> Lazy Bool
ixer b (fx, fy) = index fy (index fx b)

rhs : Vect n (Vect m (Fin n, Fin m)) -> (b : Vect n (Vect m Bool)) -> (Fin n, Fin m) -> Bool
rhs coords b f = let neigh = uncurry neighCoords f in and $ map (ixer b) neigh

gameStep : board n m -> board n m
gameStep {n} {m} b = let coords = boardCoords n m in map (map (rhs coords b)) coords 


repeatF : Nat -> (a -> a) -> a -> a
repeatF Z f = id
repeatF (S k) f = f . (repeatF k f)

-- this is way too specific, but I'm getting bored
placeBoard : board n m -> Fin n -> Fin m -> board n m
placeBoard b fx fy = updateAt fx (\v => updateAt fy (const True) v) b

blankBoard : board n m
blankBoard {n} {m} = map (map (const False)) (boardCoords n m)

mkBoard : (List (Fin n, Fin m)) -> board n m
mkBoard l = foldr (\f,b => uncurry (placeBoard b) f) blankBoard l
