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

-- okay! That worked about as well as I hoped. Thank goodness.

atomNeg : Formula -> Formula
atomNeg (Atom x) = Atom x
atomNeg (Disj x y) = Disj (atomNeg x) (atomNeg y)
atomNeg (Conj x y) = Conj (atomNeg x) (atomNeg y)
atomNeg (Imp x y) = (Imp (atomNeg x) (atomNeg y))
atomNeg (Neg (Atom x)) = Neg (Atom x)
atomNeg (Neg (Disj x y)) = atomNeg (Conj (Neg x) (Neg y))
atomNeg (Neg (Conj x y)) = atomNeg (Conj (Neg x) (Neg y))
atomNeg (Neg (Imp x y)) = atomNeg (Neg (noImp (Imp x y)))
atomNeg (Neg (Neg x)) = atomNeg x

-- alright, but this is actually a pretty annoying tradeoff to have to deal with cases that don't really exist, even though on one hand it's maybe a little simpler to just go ahead and reuse the same ADT, the auxilliary proofs will get more and more annoying

data CNF = PosAtom String | CConj CNF CNF | NegAtom String

formToCNF : Formula -> CNF 
formToCNF (Atom x) = PosAtom x
formToCNF (Disj x y) = CConj (formToCNF (Neg x)) (formToCNF (Neg y))
formToCNF (Conj x y) = CConj (formToCNF x) (formToCNF y)
formToCNF (Imp x y) = formToCNF (Disj (Neg x) y)
formToCNF (Neg (Atom x)) = NegAtom x
formToCNF (Neg (Disj x y)) = formToCNF (Conj (Neg x) (Neg y))
formToCNF (Neg (Conj x y)) = formToCNF (Disj (Neg x) (Neg y))
formToCNF (Neg (Imp x y)) = formToCNF (Conj x (Neg y))
formToCNF (Neg (Neg x)) = formToCNF x

-- I'm a little surprised the totality checker didn't complain a little about the Neg cases
-- I would have thought that they weren't decreasing the measure enough for the checker, but
-- maybe it does a little deeper search than each individual case
-- 
-- wait, I lied this isn't obviously total at all. How to fix that? Well, the obvious answer
-- is to inline far less and actually do the separate translations between languages without features

