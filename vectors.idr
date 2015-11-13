import Data.Vect
import Data.Fin

matrix : Nat -> Nat -> Type -> Type
matrix k j x = Vect k (Vect j x)

addV : Num a => Vect n a -> Vect n a -> Vect n a
addV [] [] = []
addV (x :: xs) (y :: ys) = (x + y) :: (addV xs ys)

dot : Num a => Vect n a -> Vect n a -> a
dot [] [] = 0
dot (x :: xs) (y :: ys) = (x * y) + (dot xs ys)

add : Num a => matrix n m a -> matrix n m a -> matrix n m a
add [] [] = []
add (x :: xs) (y :: ys) = (addV x y) :: (add xs ys)

row : Fin n -> matrix n m a -> Vect m a
row = index

col : Fin m -> matrix n m a -> Vect n a
col x y = map (index x) y

promote : Fin n -> Fin (n + m)
promote FZ = FZ
promote (FS x) = FS (promote x)

inject : Fin n -> Fin (S n)
inject FZ = FZ
inject (FS x) = FS (inject x)

listFins : (n : Nat) -> Vect n (Fin n)
listFins Z = []
listFins (S k) = FZ :: (map FS (listFins k))

squareMatrix : Nat -> Type -> Type
squareMatrix n = matrix n n

det : Num a => squareMatrix n a -> a
det {n} x = sum $ map thing (listFins n)
    where thing ix = dot (row ix x) (col ix x)
