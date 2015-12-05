-- Local Variables:
-- idris-load-packages: ("prelude" "effects" "contrib" "base")
-- End:

import Data.Vect
import Data.Fin

-- https://en.wikipedia.org/wiki/Netpbm_format
-- A little file for writing PPM format. Why? Because I want to do some little image things
-- in Idris like the ones in the class I helped with using that Haskell library

preamble : Nat -> Nat -> String
preamble x y = unlines ["P3",show x ++ " " ++ show y]

PPM : Nat -> Nat -> Type
PPM x y = Vect y (Vect x (Int,Int,Int))

auxFun : (Int,Int,Int) -> String
auxFun (r,g,b) = (show r) ++ " " ++ (show g) ++ " " ++ (show b)

unwordsV : Vect x String -> String
unwordsV [] = ""
unwordsV (x :: xs) = x ++ " " ++ (unwordsV xs)

unlinesV : Vect x String -> String
unlinesV [] = ""
unlinesV (x :: xs) = x ++ "\n" ++ (unlinesV xs)

ppmToString : PPM x y -> String
ppmToString p = unlinesV $ map (unwordsV . map auxFun) p

ppmToFile : PPM x y -> String -> IO (Either FileError ())
ppmToFile p file = writeFile file (ppmToString p)

-- so we'll do the same thing as the original Haskell code I saw and have a function from doubles
-- to colors and then, being given dimensions to render, create an actual PPM type
coords : Double -> Double -> Double -> Double -> (xsample : Nat) -> (ysample : Nat) -> Vect ysample (Vect xsample (Double, Double))
coords x y delx dely xsample Z = []
coords x y delx dely xsample (S k) = (?createRow (S k)) 

funToVector : (Double -> Double -> (Int,Int,Int)) -> Double -> Double -> Double -> Double -> (xsample : Nat) -> (ysample : Nat) -> PPM xsample ysample
funToVector f startx starty delx dely xsample ysample = map (map (uncurry f)) (coords startx starty delx dely xsample ysample)
