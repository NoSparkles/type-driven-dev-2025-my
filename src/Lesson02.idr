module Lesson02

import Data.Vect

-- ADT
-- Enumerator
data Direction = North | South | East | West

turn : Direction -> Direction
turn North = East
turn South = West
turn East = South
turn West = North

-- Union
data Shape = Triangle Double Double
            | Rectangle Double Double

data Picture = Primitive Shape
            | Combine Shape Shape

testPicture : Picture
testPicture = Combine (Triangle 1 1) (Triangle 0 0)

-- Generics
data Tree a = Empty | Node (Tree a) (Tree a) a
%name Tree tree, tree1, tree2

insert : Ord e => e -> Tree e -> Tree e
insert x Empty = Node Empty Empty x
insert x orig@(Node tree tree1 y) = case compare x y of
                                LT => Node (insert x tree) tree1 y
                                EQ => orig
                                GT => Node tree (insert x tree1) y

data BTree : Type -> Type where
    BEmpty : Ord a => BTree a
    BNode : Ord a => BTree a -> BTree a -> a -> BTree a
%name BTree tree, tree1, tree2

insert' : e -> BTree e -> BTree e
insert' x BEmpty = BNode BEmpty BEmpty x
insert' x orig@(BNode tree tree1 y) = case compare x y of
                            LT => BNode (insert' x tree) tree1 y
                            EQ => orig
                            GT => BNode tree (insert' x tree1) y    

-- Dependant
n : Nat
n = 4

n' : Nat
n' = S(S(Z))

minusOne : Nat -> Nat
minusOne 0 = 0
minusOne (S k) = k


data PowerSource = Petrol | Pedal

data Vehicle : PowerSource -> Type where
    Bicycle : Vehicle Pedal
    Tricycle : Vehicle Pedal
    Car : (fuel: Nat) -> Vehicle Petrol
    Bus : (fuel: Int) -> Vehicle Petrol

refuel : Vehicle Petrol -> Vehicle Petrol
refuel (Car fuel) = Car (S(fuel))
refuel (Bus fuel) = Bus (fuel + 100)
refuel Bicycle impossible


-- Lists

l : List Int
l = 1 :: 2 :: Nil

l' : List Int
l' = [1, 2, 3]

len : List a -> Nat
len [] = 0
len (_ :: xs) = S (len xs)

-- Vectors

ev : Vect 0 Int
ev = []

sev : Vect 1 Char
sev = ['a']

failing
    len' : Vect k b -> Nat
    len' xs = k

len'' : (k: Nat) -> Vect k b -> Nat
len'' k xs = k

len''' : {k: Nat} -> Vect k b -> Nat
len''' {k} _ = k

lenStr : String -> Nat
lenStr str = case unpack str of
        [] => 0  
        (x :: xs) => S (len xs) 
    
lenStr' : String -> Nat
lenStr' str = length (unpack str)


longer : String -> String -> Nat
longer str str1 = 
    let l1 = (length str) in 
    let l2 = (length str1) in
    case compare l1 l2 of
                LT => l2
                EQ => l1
                GT => l1

takeN : Nat -> List a -> List a
takeN 0 _ = []
takeN (S k) [] = []
takeN (S k) (x :: xs) = x :: takeN k xs
