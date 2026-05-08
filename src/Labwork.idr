module Labwork

import Data.Vect
import Data.Fin
import Decidable.Equality
import Data.String
import Data.Stream
import Data.Fuel

%default total

--------------------------------------------------------------------------------
--- 1. BOARD REPRESENTATION
--------------------------------------------------------------------------------

public export
BoardSize : Nat
BoardSize = 8

public export
Board : Type
Board = Vect BoardSize (Vect BoardSize Bool)

public export
emptyBoard : Board
emptyBoard = replicate BoardSize (replicate BoardSize False)

--------------------------------------------------------------------------------
--- 2. PROOFS OF VACANCY
--------------------------------------------------------------------------------

public export
data IsEmpty : (board : Board) -> (r : Fin BoardSize) -> (c : Fin BoardSize) -> Type where
  ItIsFree : (index c (index r board) = False) -> IsEmpty board r c

public export
occupiedNotFree : (index c (index r board) = True) -> IsEmpty board r c -> Void
occupiedNotFree prf (ItIsFree freePrf) = 
  let contradiction = trans (sym prf) freePrf in
  case contradiction of 
    Refl impossible

--------------------------------------------------------------------------------
--- 3. DECIDABLE CHECKING
--------------------------------------------------------------------------------

public export
checkCell : (board : Board) -> (r : Fin BoardSize) -> (c : Fin BoardSize) -> Dec (IsEmpty board r c)
checkCell board r c with (index c (index r board)) proof p
  checkCell board r c | False = Yes (ItIsFree (rewrite p in Refl))
  checkCell board r c | True  = No (\(ItIsFree contraPrf) => occupiedNotFree p (ItIsFree contraPrf))

--------------------------------------------------------------------------------
--- 4. BOARD UPDATES
--------------------------------------------------------------------------------

public export
placeBlock : (board : Board) -> (r : Fin BoardSize) -> (c : Fin BoardSize) -> Board
placeBlock board r c = 
  let targetRow = index r board
      newRow    = replaceAt c True targetRow
  in replaceAt r newRow board

--------------------------------------------------------------------------------
--- 5. SHAPE LOGIC (FIXED FOR UNIFICATION)
--------------------------------------------------------------------------------

public export
record Shape where
  constructor MkShape
  offsets : List (Int, Int)

public export
square2x2 : Shape
square2x2 = MkShape [(0,0), (0,1), (1,0), (1,1)]

public export
line3v : Shape
line3v = MkShape [(0,0), (1,0), (2,0)]

public export
line3h : Shape
line3h = MkShape [(0,0), (0,1), (0,2)]

public export
lPiece : Shape
lPiece = MkShape [(0,0), (1,0), (2,0), (2,1)]

public export
singleDot : Shape
singleDot = MkShape [(0,0)]

||| A verified list of actual board coordinates.
||| This replaces the board-dependent CanPlace to fix the recursion error.
public export
data ValidPlacement : List (Int, Int) -> Type where
  NoMore  : ValidPlacement []
  NextPos : (resR : Fin BoardSize) -> (resC : Fin BoardSize) -> 
            ValidPlacement rest -> ValidPlacement ((r, c) :: rest)

||| Corrected applyShape: It now uses ValidPlacement which doesn't change 
||| when the board is updated.
public export
applyShape : (board : Board) -> (coords : List (Int, Int)) -> ValidPlacement coords -> Board
applyShape board [] NoMore = board
applyShape board ((r, c) :: rest) (NextPos resR resC step) = 
  let boardWithBlock = placeBlock board resR resC
  in applyShape boardWithBlock rest step

--------------------------------------------------------------------------------
--- 6. SEARCH ENGINE (Generating the Proof)
--------------------------------------------------------------------------------

||| Tries to find a valid placement where all cells are currently empty.
public export
canPlaceAt : (board : Board) -> (br, bc : Int) -> (offsets : List (Int, Int)) -> 
             Maybe (ValidPlacement offsets)
canPlaceAt board br bc [] = Just NoMore
canPlaceAt board br bc ((offR, offC) :: rest) = do
  resR <- natToFin (cast (br + offR)) BoardSize
  resC <- natToFin (cast (bc + offC)) BoardSize
  case checkCell board resR resC of
    Yes _ => do
      later <- canPlaceAt board br bc rest
      Just (NextPos resR resC later)
    No _ => Nothing

--------------------------------------------------------------------------------
--- 7. LINE CLEARING (THE BLAST)
--------------------------------------------------------------------------------

public export
data RowStatus : Vect n Bool -> Type where
  Full    : RowStatus (replicate n True)
  NotFull : (row : Vect n Bool) -> RowStatus row

public export
inspectRow : (v : Vect BoardSize Bool) -> RowStatus v
inspectRow v with (decEq v (replicate BoardSize True))
  inspectRow (replicate BoardSize True) | (Yes Refl) = Full
  inspectRow v | (No _) = NotFull v

isRowFull : Vect BoardSize Bool -> Bool
isRowFull row with (inspectRow row)
  isRowFull _ | Full = True
  isRowFull _ | NotFull _ = False

||| The "Full Blast": Decides what to clear, then does it all at once.
||| A cell is cleared if its row is full OR its column is full.
public export
clearFullRows : Board -> Board
clearFullRows board = 
  let rowMask = map isRowFull board
      colMask = map isRowFull (transpose board) 
  in 
    Data.Vect.Fin.tabulate (\r => 
      Data.Vect.Fin.tabulate (\c => 
        let shouldBlast = index r rowMask || index c colMask
        in if shouldBlast then False else index c (index r board)
      )
    )

||| Tries to place a shape.
||| Returns Left originalBoard if it fails.
||| Returns Right newBoard (after blast) if it succeeds.
public export
makeMove : Board -> (br, bc : Int) -> Shape -> Either Board Board
makeMove board br bc shape with (canPlaceAt board br bc shape.offsets)
  makeMove board br bc shape | Just prf = 
    let placedBoard = applyShape board shape.offsets prf
        blastedBoard = clearFullRows placedBoard
    in Right blastedBoard
  makeMove board br bc shape | Nothing = 
    Left board

||| Generates all possible Fin indices for the board
allFins : Vect BoardSize (Fin BoardSize)
allFins = tabulate id

||| Returns True if there is at least one valid spot for the shape
hasValidMove : Board -> Shape -> Bool
hasValidMove board shape = 
  any (\r => any (\c => 
    isJust (canPlaceAt board (cast (finToNat r)) (cast (finToNat c)) shape.offsets)
  ) allFins) allFins

testBoard : Board
testBoard = [
  [False, True, True, True, True, True, True, True],
  [False, False, False, True, False, False, True, True],
  [False, False, False, True, False, False, True, True],
  [False, True, False, True, False, False, False, True],
  [False, False, False, True, False, False, False, True],
  [False, False, False, True, False, False, False, True],
  [False, False, False, True, False, False, False, True],
  [True, True, True, True, False, True, True, True]
]

testBoard2 : Board
testBoard2 = [
  [True, True, False, False, False, False, False, False],
  [False, False, False, False, False, False, False, False],
  [False, False, True, True, True, True, True, False],
  [True, True, False, False, False, False, False, False],
  [True, True, False, False, False, False, False, False],
  [True, True, False, False, False, False, False, False],
  [True, True, False, False, False, False, False, False],
  [True, True, False, False, False, False, False, False]
]

boardAfterMove : Board
boardAfterMove = case makeMove testBoard2 1 0 square2x2 of
            (Left x) => emptyBoard
            (Right x) => x

||| Converts a single row to a string representation
showRow : Vect n Bool -> String
showRow row = "|" ++ (fastConcat $ toList $ map (\b => if b then "■" else "·") row) ++ "|"

||| A custom view for the board to make it look like a grid
[GameView] Show Board where
  show board = 
    let header = "   0 1 2 3 4 5 6 7"
        divider = "  -----------------"
        -- Helper to format rows
        showRow : (Fin BoardSize, Vect BoardSize Bool) -> String
        showRow (i, row) = show (finToNat i) ++ "| " ++ (fastConcat $ toList $ map (\b => if b then "■ " else "· ") row) ++ "|"
        
        -- Zip with indices to get row numbers
        rows = toList $ map showRow (zip allFins board)
    in unlines (header :: divider :: rows ++ [divider])

||| Custom Show for Shape to render as a small grid
||| Custom Show for Shape to render as a small grid
public export
Show Shape where
  show (MkShape []) = "Empty Shape"
  show (MkShape offsets@((r, c) :: rest)) = 
    let -- 1. Find the bounds safely by starting with the first element
        rs = map fst offsets
        cs = map snd offsets
        minR = foldl min r rs
        maxR = foldl max r rs
        minC = foldl min c cs
        maxC = foldl max c cs
        
        -- 2. Create the coordinate range for the bounding box
        rowRange = [minR .. maxR]
        colRange = [minC .. maxC]
        
        -- 3. Check if a coordinate is part of the shape
        isPart : Int -> Int -> Bool
        isPart r' c' = any (\(or, oc) => or == r' && oc == c') offsets
        
        -- 4. Build the string row by row
        renderRow : Int -> String
        renderRow r' = (fastConcat $ map (\c' => if isPart r' c' then "■ " else "· ") colRange)
        
    in "\n" ++ (unlines $ map renderRow rowRange)

public export
record GameState where
  constructor MkGameState
  board : Board
  hand  : List Shape -- Our "Hand" of 2 shapes

||| A simple infinite stream of random-ish shapes
shapePool : List Shape
shapePool = [square2x2, line3v, line3h, lPiece, singleDot]

||| Cycle through the pool infinitely
allShapes : Stream Shape
allShapes = cycle shapePool


--------------------------------------------------------------------------------
--- 9. TOTAL INTERACTIVE LOOP
--------------------------------------------------------------------------------

||| Processes a turn and returns the new GameState
||| Returns Nothing if indices are out of bounds or move is illegal
processTurn : GameState -> (handIdx : Nat) -> (r, c : Int) -> Maybe GameState
processTurn (MkGameState b hand) idx r c = do
  targetShape <- nth idx hand
  case makeMove b r c targetShape of
    Left _ => Nothing 
    Right newBoard => Just (MkGameState newBoard (deleteAt idx hand))
  where
    nth : Nat -> List a -> Maybe a
    nth 0 (x::xs) = Just x
    nth (S k) (x::xs) = nth k xs
    nth _ _ = Nothing

    deleteAt : Nat -> List a -> List a
    deleteAt 0 (x::xs) = xs
    deleteAt (S k) (x::xs) = x :: deleteAt k xs
    deleteAt _ [] = []

||| The total game loop using built-in Fuel
total
gameLoop : Fuel -> GameState -> Stream Shape -> IO ()
gameLoop Dry _ _ = putStrLn "Game session ended (Out of fuel)."
gameLoop (More tank) (MkGameState b hand) rest = do
  -- 1. Refill hand if empty
  let (currentHand, nextStream) = if null hand 
                                  then (Prelude.take 2 rest, drop 2 rest) 
                                  else (hand, rest)
  
  -- 2. Display State
  putStrLn (show @{GameView} b)
  putStrLn "Your Hand:"
  let showHand = zipWith (\i, s => show i ++ ": " ++ show s) [0..1] currentHand
  putStrLn (unlines showHand)
  
  -- 3. Input
  putStr "Enter <shapeIdx> <row> <col>: "
  input <- getLine
  let cmds = map cast (words input)
  
  case cmds of
    [sIdx, r, c] => 
      case processTurn (MkGameState b currentHand) (fromInteger (cast sIdx)) r c of
        Just nextState => do
          putStrLn "--- Move Accepted ---"
          gameLoop tank nextState nextStream
        Nothing => do
          putStrLn "!!! Invalid Move !!!"
          gameLoop tank (MkGameState b currentHand) nextStream
    _ => do
      putStrLn "Error: Enter three numbers (e.g., 0 3 3)"
      gameLoop tank (MkGameState b currentHand) nextStream

||| A simple LCG for pseudo-random shapes
randomShapes : Stream Int -> List Shape -> Stream Shape
randomShapes (n :: ns) pool = 
  let idx = cast (abs n `mod` cast (length pool))
      shape = maybe singleDot id (indexOpt idx pool)
  in shape :: randomShapes ns pool
  where
    indexOpt : Nat -> List a -> Maybe a
    indexOpt 0 (x::xs) = Just x
    indexOpt (S k) (x::xs) = indexOpt k xs
    indexOpt _ _ = Nothing

seedStream : Stream Int
seedStream = iterate (\n => (n * 1103515245 + 12345) `mod` 2147483647) 12345

--------------------------------------------------------------------------------
--- 10. MAIN
--------------------------------------------------------------------------------

covering
main : IO ()
main = do
  let shapes = randomShapes seedStream [square2x2, line3v, line3h, lPiece, singleDot]
  -- Start the loop with the built-in 'forever' fuel
  gameLoop forever (MkGameState emptyBoard []) shapes
