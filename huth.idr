
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

CNF : Type
CNF = List (List Lit) -- the outer ones are conjunctions the inner lists are disjunctions

aux : List Lit -> Bool
aux [] = True
aux (x :: xs) = (elem (negLit x) xs) || (aux xs)

-- Okay I'm really confused why it can't figure out the type instance if I put cnf instead of List (List Lit).
cnfValid : CNF -> Bool
cnfValid c = all aux c

data ImpFree = IConj ImpFree ImpFree | IDisj ImpFree ImpFree | INeg ImpFree
             | IAtom String
             
impFree : Formula -> ImpFree
impFree (Atom x) = (IAtom x)
impFree (Disj x y) = IDisj (impFree x) (impFree y)
impFree (Conj x y) = IConj (impFree x) (impFree y)
impFree (Imp x y) = IDisj (INeg (impFree x)) (impFree y)
impFree (Neg x) = INeg (impFree x)

data NNF = NConj NNF NNF | NDisj NNF NNF | NLit Lit

toNNF : ImpFree -> NNF
toNNF (IConj x y) = NConj (toNNF x) (toNNF y)
toNNF (IDisj x y) = NDisj (toNNF x) (toNNF y)
toNNF (INeg (IConj x y)) = NDisj (toNNF arg1)
                                 (toNNF arg2)
    where arg1 = assert_smaller (INeg (IConj x y)) (INeg x)
          arg2 = assert_smaller (INeg (IConj x y)) (INeg y)

toNNF (INeg (IDisj x y)) = NConj (toNNF (assert_smaller (INeg (IDisj x y)) (INeg x)))
                                  (toNNF (assert_smaller (INeg (IDisj x y)) (INeg y)))
toNNF (INeg (INeg x)) = toNNF x
toNNF (INeg (IAtom x)) = NLit (NegAtom x)
toNNF (IAtom x) = NLit (PosAtom x)

accumLits : NNF -> List Lit
accumLits (NConj x y) = accumLits x ++ accumLits y -- this case won't happen in disjLift
accumLits (NDisj x y) = accumLits x ++ accumLits y
accumLits (NLit x) = [x]

disjLift : (x : NNF) -> (y : NNF) -> List (List Lit) 
disjLift (NConj x1 x2) y = (disjLift x1 y) ++ (disjLift x2 y)
disjLift x (NConj y1 y2) = (disjLift x y1) ++ (disjLift x y2)
disjLift x y = [(accumLits x) ++ (accumLits y)]

nnfTocnf : NNF -> CNF
nnfTocnf (NConj x y) = nnfTocnf x ++ nnfTocnf y
nnfTocnf (NDisj x y) = disjLift x y
nnfTocnf (NLit x) = [[x]]
