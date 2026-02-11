module Lesson02

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

