
-- Local Variables:
-- idris-load-packages: ("prelude" "effects" "contrib" "base")
-- End:


-- Here we're going to include some algorithms related to Huth and Ryan's book, for practice

data Formula = Atom String | Disj Formula Formula | Conj Formula Formula
             | Imp Formula Formula | Neg Formula
             
-- we could do a CNF conversion to a different type but I'd also like to try seeing if
-- I can do a thing of converting to the same type and actually proving that it won't
-- produce terms outside the subset

noImp : Formula -> Formula
noImp (Atom x) = (Atom x)
noImp (Disj x y) = Disj (noImp x) (noImp y)
noImp (Conj x y) = Conj (noImp x) (noImp y)
noImp (Imp x y) = Disj (Neg x) y
noImp (Neg x) = Neg (noImp x)

-- now how do we state our property? Maybe something like

noImpCorrect : (f : Formula) -> (g : Formula) -> (h : Formula) -> (Imp g h) = (noImp f) -> Void
noImpCorrect (Atom _) _ _ Refl impossible
noImpCorrect (Disj _ _) _ _ Refl impossible
noImpCorrect (Conj _ _) _ _ Refl impossible
noImpCorrect (Imp _ _) _ _ Refl impossible
noImpCorrect (Neg _) _ _ Refl impossible

data Lit = PosAtom String | NegAtom String -- yes this is really just an either type

negLit : Lit -> Lit
negLit (PosAtom x) = NegAtom x
negLit (NegAtom x) = PosAtom x

instance Eq Lit where
  (PosAtom x) == (PosAtom y) = x == y
  (NegAtom x) == (NegAtom y) = x == y
  x == y = False

cnf : Type
cnf = List (List Lit) -- the outer ones are conjunctions the inner lists are disjunctions

aux : List Lit -> Bool
aux [] = True
aux (x :: xs) = (elem (negLit x) xs) || (aux xs)

cnfValid : List (List Lit) -> Bool
cnfValid c = all aux c
