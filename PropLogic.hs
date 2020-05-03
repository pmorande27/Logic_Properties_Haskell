import Test.QuickCheck
import Data.List

data Exp = Var String |T | F |Not Exp| Exp :|: Exp | Exp :&: Exp | Exp :->: Exp | Exp :<->: Exp deriving (Eq,Show, Ord)
exp1 :: Exp
exp1 = Var "A" :<->: (Var "B" :->: (Var "C" :|: Var "D"))
showExp :: Exp -> String
showExp (Var x) = x
showExp (Not x) = "("++"Not"++showExp x ++ ")"
showExp T = "T"
showExp F = "F"
showExp (a :|: b) = "(" ++showExp a ++ ")" ++ "|" ++ "("++showExp b++")"
showExp (a :&: b) = "(" ++showExp a ++ ")" ++ "&" ++ "("++showExp b++")"
showExp (a :->: b) = "(" ++showExp a ++ ")" ++ "->" ++ "("++showExp b++")"
showExp (a :<->: b)= "(" ++showExp a ++ ")" ++ "<->" ++ "("++showExp b++")"
type Valuation = [(String, Bool)]
val  :: Valuation
val = [("A", True), ("B", False), ("C", True), ("D", False)]
eval :: Valuation -> Exp -> Bool
eval y (Var x) = lookup x y
    where
    lookup x y = the [b | (c,b)<- y , x == c]
    the [x] = x
eval v T = True
eval v (Not x) = not (eval v x)
eval v F = False
eval v (a :|: b) = eval v a || eval v b
eval v (a :&: b) = eval v a && eval v b
eval v (a :->: b) = not (eval v a) || eval v b
eval v (a :<->: b) = eval v a == eval v b
removeimplications :: Exp -> Exp
removeimplications (Var x) = Var x
removeimplications T = T
removeimplications F = F 
removeimplications (Not x) = Not (removeimplications x)
removeimplications ( a :|: b) = removeimplications a :|: removeimplications b 
removeimplications (a :&: b) = removeimplications a :&: removeimplications b 
removeimplications (a :->: b) = ((Not(removeimplications a)) :|: removeimplications b)
removeimplications (p :<->: q) = removeimplications (p :->: q) :&: removeimplications (q :->: p)
prop1 :: Exp -> Exp -> Bool
prop1 a b =  ((Not(removeimplications a)) :|: removeimplications b) == (removeimplications ((Not a) :|: b))
removeneg :: Exp -> Exp
removeneg (Var x) = Var x
removeneg T = T
removeneg F = F 
removeneg (Not (Var x)) = Var x
removeneg ( Not (Not x)) = x
removeneg (Not (a :|: b)) = removeneg (Not a) :&: removeneg (Not b)
removeneg ( a :|: b) = removeneg a :|: removeneg b 
removeneg (Not (a :&: b)) = removeneg (Not a) :|: removeneg (Not b)
removeneg (a :&: b) = removeneg a :&: removeneg b
distribute :: Exp -> Exp
-- Literals, no change
distribute (Var x) = (Var x)
distribute (Not (Var x)) = (Not (Var x))
distribute (T) = T
distribute (F) = F
-- Conjunction, no change, try sub-expressions
distribute (p :&: q) = distribute p :&: distribute q
-- Disjunction, first turn the disjuncts into CNF, then use helper to distribute
distribute (p :|: q) = helper (distribute p) (distribute q)
    where
    helper (a :&: b) c = helper a c :&: helper b c
    helper a (b :&: c) = helper a b  :&: helper a c
    helper a b = a :|: b

cnf :: Exp -> Exp
cnf = distribute . removeneg . removeimplications
--Satisfiable--
phy = (Var "A" :|: Not (Var "C") :|: Not (Var "D")) :&: (Var "A" :|: Var "C" :|: Not (Var "D")) :&: (Var "A" :|: Var "D") :&: (Var "B" :|: Not (Var "C")) :&: Var "A"


searchvar :: Exp -> [String]
searchvar (Var x) = [x]
searchvar (Not x ) = nub (searchvar x)
searchvar (a :|: b) = nub ( searchvar a ++ searchvar b)
searchvar ( a :&: b) = nub (searchvar a ++ searchvar b)
searchvar ( a :->: b) = nub (searchvar a ++ searchvar b)
searchvar (a :<->: b) = nub (searchvar a ++ searchvar b)
generateVal :: [String] -> [Valuation]
generateVal [] = [[]]
generateVal (x:xs) = sort [(x,y):e | y <- [True,False], e <- generateVal xs]

satisfiable :: Exp -> Bool
satisfiable x = or [eval v x | v<-(generateVal (searchvar x))]
numbersatisfiable :: Exp -> Int
numbersatisfiable x = sum [1 | v <-(generateVal (searchvar x)) , eval v x]