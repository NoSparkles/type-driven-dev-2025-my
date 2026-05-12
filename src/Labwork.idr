module Labwork

import Data.Vect
import Data.Fin
import Decidable.Equality
import Data.String
import Data.Stream
import Data.Fuel
import Data.List.Elem

%default total

public export
BoardSize : Nat
BoardSize = 8

public export
Board : Type
Board = Vect BoardSize (Vect BoardSize Bool)

public export
emptyBoard : Board
emptyBoard = replicate BoardSize (replicate BoardSize False)

public export
data IsEmpty : (board : Board) -> (r : Fin BoardSize) -> (c : Fin BoardSize) -> Type where
  ItIsFree : (index c (index r board) = False) -> IsEmpty board r c

public export
occupiedNotFree : (index c (index r board) = True) -> IsEmpty board r c -> Void
occupiedNotFree prf (ItIsFree freePrf) = 
  let contradiction = trans (sym prf) freePrf in
  case contradiction of 
    Refl impossible

public export
checkCell : (board : Board) -> (r : Fin BoardSize) -> (c : Fin BoardSize) -> Dec (IsEmpty board r c)
checkCell board r c with (index c (index r board)) proof p
  checkCell board r c | False = Yes (ItIsFree (rewrite p in Refl))
  checkCell board r c | True  = No (\(ItIsFree contraPrf) => occupiedNotFree p (ItIsFree contraPrf))

public export
placeBlock : (board : Board) -> (r : Fin BoardSize) -> (c : Fin BoardSize) -> Board
placeBlock board r c = 
  let targetRow = index r board
      newRow = replaceAt c True targetRow
  in replaceAt r newRow board

public export
record Shape where
  constructor MkShape
  offsets : List (Fin BoardSize, Fin BoardSize)

iPieceV : Shape
iPieceV = MkShape [(0,0), (1,0), (2,0), (3,0)]

iPieceH : Shape
iPieceH = MkShape [(0,0), (0,1), (0,2), (0,3)]

tUp : Shape
tUp = MkShape [(0,1), (1,0), (1,1), (1,2)]

tDown : Shape
tDown = MkShape [(0,0), (0,1), (0,2), (1,1)]

tLeft : Shape
tLeft  = MkShape [(0,1), (1,0), (1,1), (2,1)]

tRight : Shape
tRight = MkShape [(0,0), (1,0), (1,1), (2,0)]

lRight1 : Shape
lRight1 = MkShape [(0,0), (1,0), (2,0), (2,1)]

lRight2 : Shape
lRight2 = MkShape [(0,0), (0,1), (0,2), (1,0)]

lRight3 : Shape
lRight3 = MkShape [(0,0), (0,1), (1,1), (2,1)]

lRight4 : Shape
lRight4 = MkShape [(0,2), (1,0), (1,1), (1,2)]

jLeft1 : Shape
jLeft1 = MkShape [(0,1), (1,1), (2,1), (2,0)]

jLeft2 : Shape
jLeft2 = MkShape [(0,0), (0,1), (0,2), (1,2)]

jLeft3 : Shape
jLeft3 = MkShape [(0,0), (0,1), (1,0), (2,0)]

jLeft4 : Shape
jLeft4 = MkShape [(0,0), (1,0), (1,1), (1,2)]

sPieceH : Shape
sPieceH = MkShape [(0,1), (0,2), (1,0), (1,1)]
sPieceV : Shape
sPieceV = MkShape [(0,0), (1,0), (1,1), (2,1)]

zPieceH : Shape
zPieceH = MkShape [(0,0), (0,1), (1,1), (1,2)]

zPieceV : Shape
zPieceV = MkShape [(0,1), (1,0), (1,1), (2,0)]

oPiece : Shape
oPiece = MkShape [(0,0), (0,1), (1,0), (1,1)]

singleDot : Shape
singleDot = MkShape [(0,0)]

line3v : Shape
line3v = MkShape [(0,0), (1,0), (2,0)]

line3h : Shape
line3h = MkShape [(0,0), (0,1), (0,2)]

public export
data BoundedOffset : (base : Fin BoardSize) -> (offset : Fin BoardSize) -> Type where
  MkBoundedOffset : {base, offset : Fin BoardSize} ->
                    (res : Fin BoardSize) ->
                    (natToFin (finToNat base + finToNat offset) BoardSize = Just res) ->
                    BoundedOffset base offset

public export
data OffsetValid : Board -> (br, bc : Fin BoardSize) -> (offR, offC : Fin BoardSize) -> Type where
  MkOffsetValid : {board : Board} -> {br, bc, offR, offC : Fin BoardSize} ->
                  (resR, resC : Fin BoardSize) ->
                  (IsEmpty board resR resC) ->
                  (BoundedOffset br offR) ->
                  (BoundedOffset bc offC) ->
                  OffsetValid board br bc offR offC

public export
data ValidPlacement : Board -> (br, bc : Fin BoardSize) -> Shape -> Type where
  NoMore  : ValidPlacement board br bc (MkShape [])
  NextPos : {offR, offC : Fin BoardSize} ->
            OffsetValid board br bc offR offC ->
            ValidPlacement board br bc (MkShape rest) ->
            ValidPlacement board br bc (MkShape ((offR, offC) :: rest))

public export
applyPlacement : (currentBoard : Board) -> ValidPlacement board br bc s -> Board
applyPlacement currentBoard NoMore = currentBoard
applyPlacement currentBoard (NextPos (MkOffsetValid resR resC _ _ _) rest) = 
  let nextBoard = placeBlock currentBoard resR resC
  in applyPlacement nextBoard rest

public export
applyShape : (board : Board) -> (br, bc : Fin BoardSize) -> (s : Shape) -> 
             ValidPlacement board br bc s -> Board
applyShape board br bc s prf = applyPlacement board prf

checkBounds : (b : Fin BoardSize) -> (o : Fin BoardSize) -> Maybe (BoundedOffset b o)
checkBounds b o with (natToFin (finToNat b + finToNat o) BoardSize) proof p
  checkBounds b o | Just res = Just (MkBoundedOffset res p)
  checkBounds b o | Nothing  = Nothing

public export
canPlaceAt : (board : Board) -> (br, bc : Fin BoardSize) -> (s : Shape) -> 
             Maybe (ValidPlacement board br bc s)
canPlaceAt board br bc (MkShape []) = Just NoMore
canPlaceAt board br bc (MkShape ((offR, offC) :: rest)) = do
  -- 1. Verify math is within 0-7
  proofR@(MkBoundedOffset resR _) <- checkBounds br offR
  proofC@(MkBoundedOffset resC _) <- checkBounds bc offC
  
  -- 2. Verify cell is empty
  case checkCell board resR resC of
    Yes emptyPrf => do
      later <- canPlaceAt board br bc (MkShape rest)
      -- 3. Construct the verified placement
      Just (NextPos (MkOffsetValid resR resC emptyPrf proofR proofC) later)
    No _ => Nothing

allFins : Vect BoardSize (Fin BoardSize)
allFins = tabulate id

public export
MovePossible : Board -> List Shape -> Type
MovePossible board hand = 
  (s : Shape ** (br : Fin BoardSize ** (bc : Fin BoardSize ** ValidPlacement board br bc s)))

findMove : (board : Board) -> (hand : List Shape) -> Maybe (MovePossible board hand)
findMove board [] = Nothing
findMove board (s :: ss) = 
  case searchBoard board s of
    Just (br ** (bc ** prf)) => Just (s ** (br ** (bc ** prf)))
    Nothing => findMove board ss
  where
    searchBoard : (b : Board) -> (sh : Shape) -> 
                  Maybe (br : Fin BoardSize ** (bc : Fin BoardSize ** ValidPlacement b br bc sh))
    searchBoard b sh = firstJust (toList [(r, c) | r <- allFins, c <- allFins])
      where 
        firstJust : List (Fin BoardSize, Fin BoardSize) -> 
                    Maybe (r : Fin BoardSize ** (c : Fin BoardSize ** ValidPlacement b r c sh))
        firstJust [] = Nothing
        firstJust ((r, c) :: xs) = 
          case canPlaceAt b r c sh of
            Just prf => Just (r ** (c ** prf))
            Nothing  => firstJust xs

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

public export
makeMove : Board -> (br, bc : Fin BoardSize) -> Shape -> Either Board Board
makeMove board br bc shape with (canPlaceAt board br bc shape)
  makeMove board br bc shape | Just prf = 
    let placedBoard = applyShape board br bc shape prf
        blastedBoard = clearFullRows placedBoard
    in Right blastedBoard
  makeMove board br bc shape | Nothing = 
    Left board

public export
hasValidMove : Board -> Shape -> Bool
hasValidMove board shape = 
  any (\r => any (\c => 
    isJust (canPlaceAt board r c shape)
  ) allFins) allFins
  where
    isJust : Maybe a -> Bool
    isJust (Just _) = True
    isJust Nothing  = False

showRow : Vect n Bool -> String
showRow row = "|" ++ (fastConcat $ toList $ map (\b => if b then "■" else "·") row) ++ "|"

[GameView] Show Board where
  show board = 
    let header = "   0 1 2 3 4 5 6 7"
        divider = "  -----------------"
        
        showRow : (Fin BoardSize, Vect BoardSize Bool) -> String
        showRow (i, row) = show (finToNat i) ++ "| " ++ (fastConcat $ toList $ map (\b => if b then "■ " else "· ") row) ++ "|"
        
        rows = toList $ map showRow (zip allFins board)
    in unlines (header :: divider :: rows ++ [divider])

public export
Show Shape where
  show (MkShape []) = "Empty Shape"
  show (MkShape offsets@((fR, fC) :: rest)) = 
    let
      coords : List (Integer, Integer)
      coords = map (\(fr, fc) => (the Integer (cast (finToNat fr)), the Integer (cast (finToNat fc)))) offsets

      -- Use 'the Integer' here to clarify we are casting Nat -> Integer
      startR : Integer
      startR = the Integer (cast (finToNat fR))
      
      startC : Integer
      startC = the Integer (cast (finToNat fC))
      
      rs = map fst coords
      cs = map snd coords
      
      minR = foldl min startR rs
      maxR = foldl max startR rs
      minC = foldl min startC cs
      maxC = foldl max startC cs
      
      rowRange = [minR .. maxR]
      colRange = [minC .. maxC]
      
      isPart : Integer -> Integer -> Bool
      isPart r' c' = any (\(or, oc) => or == r' && oc == c') coords
      
      renderRow : Integer -> String
      renderRow r' = (fastConcat $ map (\c' => if isPart r' c' then "■ " else "· ") colRange)
        
    in "\n" ++ (unlines $ map renderRow rowRange)

public export
record GameState where
  constructor MkGameState
  board : Board
  hand  : List Shape

public export
shapePool : List Shape
shapePool = [ 
  iPieceV, iPieceH, 
  tUp, tDown, tLeft, tRight,
  lRight1, lRight2, lRight3, lRight4,
  jLeft1, jLeft2, jLeft3, jLeft4,
  sPieceH, sPieceV, 
  zPieceH, zPieceV,
  oPiece, 
  singleDot, line3v, line3h 
]

allShapes : Stream Shape
allShapes = cycle shapePool

nth : Nat -> List a -> Maybe a
nth 0 (x::xs) = Just x
nth (S k) (x::xs) = nth k xs
nth _ _ = Nothing

deleteAt : Nat -> List a -> List a
deleteAt 0 (x::xs) = xs
deleteAt (S k) (x::xs) = x :: deleteAt k xs
deleteAt _ [] = []

processTurn : GameState -> (handIdx : Nat) -> (r, c : Fin BoardSize) -> Maybe GameState
processTurn (MkGameState b hand) idx r c with (nth idx hand)
  processTurn (MkGameState b hand) idx r c | Nothing = Nothing
  processTurn (MkGameState b hand) idx r c | Just targetShape with (makeMove b r c targetShape)
    processTurn (MkGameState b hand) idx r c | Just targetShape | Left _ = Nothing
    processTurn (MkGameState b hand) idx r c | Just targetShape | Right newBoard = 
      Just (MkGameState newBoard (deleteAt idx hand))

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

gameLoop : Fuel -> GameState -> Stream Shape -> IO ()
gameLoop Dry _ _ = putStrLn "Game session ended (Out of fuel)." 
gameLoop (More tank) (MkGameState b hand) rest = do
  -- 1. Refresh hand if empty
  let (currentHand, nextStream) = if null hand 
                                  then (Prelude.take 3 rest, drop 3 rest) 
                                  else (hand, rest) 
  
  -- 2. Display Board and Hand
  putStrLn (show @{GameView} b) 
  putStrLn "Your Hand:"
  let handDisplay = zipWith (\i, s => show i ++ ":" ++ show s) [0..length currentHand] currentHand 
  putStrLn (unlines handDisplay) 

  -- 3. Check for Game Over using the Dependent Pair
  case findMove b currentHand of
    Nothing => do
      putStrLn "!!! GAME OVER !!! No more moves possible with the remaining hand." 
      putStrLn "Restarting game..."
      gameLoop tank (MkGameState emptyBoard []) nextStream 
      
    Just (s ** r ** c ** prf) => do
      putStr "Enter <shapeIdx> <row> <col>: "
      input <- getLine 
      let inputWords = words input 
      
      case inputWords of
        [sIdxStr, rStr, cStr] => do
          let sIdx = cast {to=Integer} sIdxStr
          let rVal = cast {to=Integer} rStr
          let cVal = cast {to=Integer} cStr
          
          -- 4. Convert to Nat for natToFin
          let rNat = the Nat (fromInteger rVal)
          let cNat = the Nat (fromInteger cVal)

          case (natToFin rNat BoardSize, natToFin cNat BoardSize) of
            (Just rFin, Just cFin) => do
              -- Pass the Fins directly to processTurn
              case processTurn (MkGameState b currentHand) (fromInteger sIdx) rFin cFin of
                Just nextState => do
                  putStrLn "--- Move Accepted ---"
                  gameLoop tank nextState nextStream 
                Nothing => do
                  putStrLn "!!! Invalid Move (Blocked or Bad Shape) !!!" 
                  gameLoop tank (MkGameState b currentHand) nextStream 
            _ => do
              -- This is the "contradiction" branch: one of the inputs was > 7 or < 0
              putStrLn "!!! Error: Coordinates must be between 0 and 7 !!!"
              gameLoop tank (MkGameState b currentHand) nextStream
                  
        _ => do
          putStrLn "Error: Use format '0 3 3'" 
          gameLoop tank (MkGameState b currentHand) nextStream

covering
main : IO ()
main = do
  let shapes = randomShapes seedStream shapePool
  gameLoop forever (MkGameState emptyBoard []) shapes
