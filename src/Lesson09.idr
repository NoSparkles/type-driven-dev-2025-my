module Lesson09

import Data.List
import Data.List.Views
import Data.Nat.Views
import Data.Nat
import Decidable.Equality.Core

%default total


namespace Last
  
  data ListLast : List a -> Type where
    Empty : ListLast []
    NonEmpty : (xs : List a) -> (x : a) -> ListLast (xs ++ [x])

  public export
  listLast : (xs : List a) -> ListLast xs
  listLast [] = Empty
  listLast (x :: xs) = case listLast xs of
                            Empty => NonEmpty [] x
                            (NonEmpty ys y) => NonEmpty (x :: ys) y

  describeLastHelper : Show a => (input : List a) -> ListLast input -> String
  describeLastHelper [] Empty = "Empty"
  describeLastHelper (xs ++ [x]) (NonEmpty xs x) = "Last element: " ++ show x

  public export
  describeLast : Show a => List a -> String
  describeLast xs = describeLastHelper xs (listLast xs)

  describeLast' : Show a => List a -> String
  describeLast' xs with (listLast xs)
    describeLast' [] | Empty = ?describeLast'_rhs_rhss_0
    describeLast' (ys ++ [x]) | (NonEmpty ys x) = ?describeLast'_rhs_rhss_1

  covering
  reverse' : List a -> List a
  reverse' xs with (listLast xs)
    reverse' [] | Empty = []
    reverse' (ys ++ [x]) | (NonEmpty ys x) = x :: (reverse' ys)

namespace Merge
  data SplitList : List a -> Type where
    SplitNil : SplitList []
    SplitOne : (x : a) -> SplitList [x]
    SplitPair : (lefts : List a) -> (rights : List a) -> SplitList (lefts ++ rights)

  public export
  splitList : (input : List a) -> SplitList input
  splitList xs = splitListHelp xs xs
    where
      splitListHelp : List a -> (xs : List a) -> SplitList xs
      splitListHelp _ [] = SplitNil
      splitListHelp _ [x] = SplitOne x
      splitListHelp (_ :: _ :: counter) (x :: xs) =
        case splitListHelp counter xs of
          SplitNil => SplitOne x
          (SplitOne y) => SplitPair [x] [y]
          (SplitPair ls rs) => SplitPair (x :: ls) rs
      splitListHelp _ xs = SplitPair [] xs

  covering
  public export
  mergeSort : Ord a => List a -> List a
  mergeSort xs with (splitList xs)
    mergeSort [] | SplitNil = []
    mergeSort [x] | (SplitOne x) = [x]
    mergeSort (lefts ++ rights) | (SplitPair lefts rights) =
      merge (mergeSort lefts) (mergeSort rights)

namespace Rec
  data SnocList' : List a -> Type where
    Empty : SnocList' []
    Snoc : (xs : List a) -> (x : a) -> (rec : SnocList' xs) -> SnocList' (xs ++ [x])

  snocListHelper :
        {xs : List a} -> (snoc : SnocList' xs) ->
        (rest : List a) -> SnocList' (xs ++ rest)
  snocListHelper snoc [] =
        rewrite appendNilRightNeutral xs in snoc
  snocListHelper {xs} snoc (x :: ys) =
        rewrite appendAssociative xs [x] ys in
        snocListHelper (Snoc xs x snoc) ys

  snocList' : (xs : List a) -> SnocList' xs
  snocList' xs = snocListHelper Empty xs

  reverseHelper : (input : List a) -> SnocList' input -> List a
  reverseHelper [] Empty = []
  reverseHelper (xs ++ [x]) (Snoc xs x rec) = x :: reverseHelper xs rec

  reverse' : List a -> List a
  reverse' xs = reverseHelper xs (snocList' xs)

  reverse'': List a -> List a
  reverse'' xs with (snocList' xs)
    reverse'' [] | Empty = []
    reverse'' (ys ++ [x]) | (Snoc ys x rec) = x :: reverse'' ys | rec

namespace Vanilla
  mergeSort' : Ord a => List a -> List a
  mergeSort' xs with (splitRec xs)
    mergeSort' [] | SplitRecNil = []
    mergeSort' [x] | (SplitRecOne x) = [x]
    mergeSort' (lefts ++ rights) | (SplitRecPair lefts rights lrec rrec) =
      merge (mergeSort' lefts | lrec) (mergeSort' rights | rrec)
   

data TakeN : List a -> Type where
    Fewer : (xs : List a) -> TakeN xs
    Enough : (lefts : List a) -> (rights : List a) -> TakeN (lefts ++ rights)

takeN : (n : Nat) -> (input : List a) -> TakeN input
takeN 0 [] = Enough [] []
takeN (S k) [] = Fewer []
takeN 0 (x :: xs) = Enough [] (x :: xs)
takeN (S k) (x :: xs) = case takeN k xs of
            (Fewer xs) => Fewer (x :: xs)
            (Enough lefts rights) => Enough (x :: lefts) (rights)

covering
groupByN : (n : Nat) -> (xs : List a) -> List (List a)
groupByN 0 xs = []
groupByN (S k) xs with (takeN (S k) xs)
  groupByN (S k) [] | Fewer [] = []
  groupByN (S k) xs | Fewer xs = [xs]
  groupByN (S k) (lefts ++ rights) | (Enough lefts rights) = lefts :: groupByN (S k) rights

halves : List a -> (List a, List a)
halves xs with (takeN ((length xs) `div` 2) xs)
  halves xs | (Fewer xs) = (xs, [])
  halves (lefts ++ rights) | (Enough lefts rights) = (lefts, rights)

isSuffix : Eq a => List a -> List a -> Bool
isSuffix xs ys with (snocList xs)
  isSuffix xs ys | with_pat with (snocList ys)
    isSuffix [] [] | Empty | Empty = True
    isSuffix [] (xs ++ [x]) | Empty | (Snoc x xs rec) = True
    isSuffix (zs ++ [x]) [] | (Snoc x zs rec) | Empty = False
    isSuffix (zs ++ [x]) (xs ++ [y]) | (Snoc x zs rec) | (Snoc y xs z) = 
            case isSuffix zs xs | rec of 
                False => False
                True => case x == y of
                    False => False
                    True => True

toBinary : Nat -> String
toBinary k with (halfRec k)
  toBinary 0 | HalfRecZ = "0"
  toBinary (n + n) | (HalfRecEven n rec) = (toBinary n | rec) ++ "0"
  toBinary (S (n + n)) | (HalfRecOdd n rec) = case (toBinary n | rec) of 
                        "0" => "1"
                        a => a ++ "1"
