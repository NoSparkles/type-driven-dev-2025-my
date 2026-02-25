module Lesson03

import Data.Vect
import Data.Fin

index' : Fin k -> Vect k a -> a
index' FZ (x :: xs) = x
index' (FS x) (y :: xs) = index' x xs

-- format "%s = %d" : String -> Int -> String
-- format "Hello" : String
-- format "%d %d" : Int -> Int -> String


data Format = Number Format |
            Str Format |
            Lit String Format |
            End

-- "%s = %d" -> Format
-- Str (Lit ' ' (Lit '=' (Lit ' ' (Number End))))

FormatType : Format -> Type
FormatType (Number x) = Int -> FormatType x
FormatType (Str x) = String -> FormatType x
FormatType (Lit _ x) = FormatType x
FormatType End = String


toFormat : List Char -> Format
toFormat [] = End
toFormat ('%' :: 's' :: xs) = Str (toFormat xs)
toFormat ('%' :: 'd' :: xs) = Number (toFormat xs)
toFormat (x :: xs) = Lit (pack [x]) (toFormat xs)

format : (fmt : Format) -> String -> FormatType fmt
format (Number x) acc = \i => format x (acc ++ show i)
format (Str x) acc = \str => format x (acc ++ str)
format (Lit c x) acc = format x (acc ++ c)
format End acc = acc

Eq Format where
    (Number x) == (Number y) = x == y
    (Str x) == (Str y) = x == y
    (Lit c x) == (Lit d y) = x == y && c == d
    End == End = True
    _ == _ = False

interface FuzzyEq a where
    (~==~) : a -> a -> Bool


FuzzyEq Int where
    (~==~) a b = a - b <= 1

-- Practice work

format' : (fmt : String) -> FormatType (toFormat (unpack fmt))
format' fmt = format'' (toFormat (unpack fmt)) "" 
    where
        format'' : (fmt : Format) -> String -> FormatType fmt
        format'' (Number x) acc = \i => format'' x (acc ++ show i)
        format'' (Str x) acc = \str => format'' x (acc ++ str)
        format'' (Lit c x) acc = format'' x (acc ++ c)
        format'' End acc = acc


interface PlusPlusPlus a where
    (+++) : String -> a -> String
infixl 5 +++

PlusPlusPlus Int where
    a +++ c = a ++ show c

PlusPlusPlus String where
    a +++ c = a ++ c

PlusPlusPlus Char where
    a +++ c = a ++ (pack [c])


append' : Vect k a -> Vect l a -> Vect (l + k) a
append' xs [] = xs
append' xs (x :: ys) = x :: append' xs ys


addNat : Nat -> Nat -> Nat
addNat 0 j = j
addNat (S k) j = S(addNat k j)
