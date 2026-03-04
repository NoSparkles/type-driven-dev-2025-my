module Lesson04

import Data.Vect
import Data.String
import System.REPL

AdderType : (Num : Nat) -> Type
AdderType 0 = Int
AdderType (S k) = Int -> AdderType k

adder : (num : Nat) -> (acc : Int) -> AdderType num
adder 0 acc = acc
adder (S k) acc = \val => adder k (acc + val)

record StringDataStore where
    constructor MkStringDataStore
    size : Nat
    items: Vect size String

one : StringDataStore
one = MkStringDataStore 1 ["Hello"]

two : StringDataStore
two = {items := ["1", "2"], size := 2} one

two' : StringDataStore
two' = { size $= S, items $= ("New" ::) } one

addStringToTail : (items : Vect size String) -> (str : String) -> Vect (S size) String
addStringToTail [] str = [str]
addStringToTail (x :: xs) str = x :: (addStringToTail xs str)

addToStringDataStore : StringDataStore -> String -> StringDataStore
addToStringDataStore (MkStringDataStore size items) str = MkStringDataStore (S size) (addStringToTail items str)

data Schema = SInt | SString | (.+.) Schema Schema
infixr 5 .+.

SchemaType : Schema -> Type
SchemaType SInt = Int
SchemaType SString = String
SchemaType (x .+. y) = (SchemaType x, SchemaType y)

record DataStore where
    constructor MkDataStore
    schema : Schema
    size : Nat
    items: Vect size (SchemaType schema)

addToTail : Vect s t -> t -> Vect  (S s) t
addToTail [] val = [val]
addToTail (x :: xs) val = x :: (addToTail xs val)

addToStore : (ds : DataStore) -> (SchemaType ds.schema) -> DataStore
addToStore ds x = {size := S ds.size, items := addToTail ds.items x} ds

empty : DataStore
empty = MkDataStore (SInt .+. SString) _ []

readNumber : IO (Maybe Nat)
readNumber = do
    input <- getLine
    if all isDigit (unpack input)
        then pure (Just (cast input))
        else pure Nothing

readTwoNumbers : IO (Maybe (Nat, Nat))
readTwoNumbers = do
    Just a1 <- readNumber | Nothing => pure Nothing
    Just a2 <- readNumber | Nothing => pure Nothing
    pure (Just (a1, a2))

showSchema : (schema: Schema) -> SchemaType schema -> String
showSchema SInt t = show t
showSchema SString t = t
showSchema (x .+. y) (valx, valy) = "(" ++ showSchema x valx ++ ", " ++ showSchema y valy ++ ")"

showAll : DataStore -> String
showAll ds = (show (map (showSchema ds.schema) ds.items)) ++ "\n"

strToSchema : (schema: Schema) -> String -> Maybe (SchemaType schema)
strToSchema SInt str = Just (the Int (cast str))
strToSchema SString str = Just str
strToSchema (x .+. y) str = case span (\c => c /= ' ') (unpack str) of
                    (z, ' ' :: w) => Just ((strToSchema x (pack z), strToSchema y (pack w)))
                    _ => Nothing



process : DataStore -> String -> Maybe (String, DataStore)
process store "show" = Just (showAll store, store)
process store str = case span (\c => c /= ' ') (unpack str) of
                (['a', 'd', 'd'], ' ' :: xs) => 
                    let newStore = addToStore store (strToSchema store.schema (pack xs)) in
                    Just (showAll newStore, store)
                _=> Nothing

main : IO ()
main = replWith (MkDataStore (SInt .+. SString) _ [(1, "fsda"), (132, "fdsa"), (123, "fds")]) "Enter Command: " process

