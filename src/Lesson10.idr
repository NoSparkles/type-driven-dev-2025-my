module Lesson10
import Data.Bits
import Data.Stream
import Data.Primitives.Views
import System

import Data.Bits
import Data.Stream
import Data.Primitives.Views
import System
%default total

namespace Label

    export
    labelFrom : Integer -> List a -> List (Integer, a)
    labelFrom i [] = []
    labelFrom i (x :: xs) = (i, x) :: (labelFrom (i+1) xs)

    export
    label : List a -> List (Integer, a)
    label = labelFrom 0

    failing
        countFrom : Integer -> List Integer
        countFrom n = n :: (countFrom (n+1))

    public export
    data InfList : Type -> Type where
        (::) : (value : e) -> Inf (InfList e) -> InfList e

    export
    countFrom : Integer -> InfList Integer
    countFrom i = i :: (countFrom (i+1))

    export
    getPrefix : (count : Nat) -> InfList a -> List a
    getPrefix 0 x = []
    getPrefix (S k) (value :: x) = value :: (getPrefix k (x))

    {-
        Functions are total if they:
          - cover all the cases
          - deconstructing a value and processing recursively its argument (which is smaller).
          - a function is productive.
    -}

    {-
        Recursion - consumes data
        CoRecursion - produces data.
    -}

namespace S

    export
    labelWith : Stream l -> List a -> List (l, a)
    labelWith s [] = []
    labelWith (y :: z) (x :: xs) = (y, x) :: labelWith z xs

    export
    label : List a -> List (Integer, a)
    label l = labelWith (iterate (+1) 0) l


namespace F

    public export
    data InfIO : Type where
        Do : IO a -> (a -> Inf InfIO) -> InfIO

    export
    loopPrint : String -> InfIO
    loopPrint msg = Do (putStrLn msg) (\_ => loopPrint msg)

    export
    covering -- Non-terminating for now.
    run' : InfIO -> IO ()
    run' (Do action cont) = do res <- action
                               run' (cont res)


    public export
    data Fuel = Dry | More Fuel

    export
    tank : Nat -> Fuel
    tank 0 = Dry
    tank (S k) = More (tank k)

    export -- Now it's total
    run : Fuel -> InfIO -> IO ()
    run Dry y = putStrLn "Out of fuel..."
    run (More f) (Do act cnt) = do res <- act
                                   run f (cnt res)

namespace F2

    public export
    data Fuel' = Dry | More (Lazy Fuel')

    export
    covering -- This cannot be total.
    forever : Fuel'
    forever = More forever

    export
    tank : Nat -> Fuel'
    tank 0 = Dry
    tank (S k) = More (tank k)

    export -- Now it's total
    run : Fuel' -> InfIO -> IO ()
    run Dry y = putStrLn "Out of fuel..."
    run (More f) (Do act cnt) = do res <- act
                                   run f (cnt res)

    covering
    main : IO ()
    main = run (forever) (F.loopPrint "a")


everyOther : Stream a -> Stream a
everyOther (a1 :: x) = a1 :: (everyOther (skipValue x))
    where
        skipValue : Stream a -> Stream a
        skipValue (x :: y) =  y



nextVal : Int -> Int
nextVal seed = (153453525 * seed + 2342353543223)

randomStream : Int -> Stream Int
randomStream seed = 
  let next = nextVal seed
      x = (next `mod` 100) + 1 
  in x :: randomStream next

total
quiz : Stream Int -> (score : Nat) -> F.InfIO
quiz (x1 :: x2 :: xs) score =
    F.Do (putStrLn ("Score: " ++ show score ++ ". What is " ++ show x1 ++ " * " ++ show x2 ++ "?")) 
    (\_ => F.Do getLine 
    (\answer => if cast answer == (x1 * x2)
            then F.Do (putStrLn "Correct!") 
                (\_ => quiz xs (score + 1))
            else F.Do (putStrLn ("Wrong! The answer was " ++ show (x1 * x2))) 
                (\_ => quiz xs score)
    ))

covering
main : IO ()
main = do
    let stream = randomStream 423424
    F2.run F2.forever (quiz stream 0)
