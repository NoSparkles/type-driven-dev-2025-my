module Labwork

import Data.Vect
import Data.Fin
import Decidable.Equality
import Data.String
import Data.Stream
import Data.Fuel
import Data.List.Elem

%default total

BoardSize : Nat
BoardSize = 8

Board : Type
Board = Vect BoardSize (Vect BoardSize Bool)

emptyBoard : Board
emptyBoard = replicate BoardSize (replicate BoardSize False)

data IsEmpty : (board : Board) -> (r : Fin BoardSize) -> (c : Fin BoardSize) -> Type where
  ItIsFree : (index c (index r board) = False) -> IsEmpty board r c

occupiedNotFree : (index c (index r board) = True) -> IsEmpty board r c -> Void
occupiedNotFree prf (ItIsFree freePrf) = 
  let contradiction = trans (sym prf) freePrf in
  case contradiction of 
    Refl impossible

checkCell : (board : Board) -> (r : Fin BoardSize) -> (c : Fin BoardSize) -> Dec (IsEmpty board r c)
checkCell board r c with (index c (index r board)) proof p
  checkCell board r c | False = Yes (ItIsFree (rewrite p in Refl))
  checkCell board r c | True  = No (\(ItIsFree contraPrf) => occupiedNotFree p (ItIsFree contraPrf))

placeBlock : (board : Board) -> (r : Fin BoardSize) -> (c : Fin BoardSize) -> Board
placeBlock board r c = 
  let targetRow = index r board
      newRow = replaceAt c True targetRow
  in replaceAt r newRow board

record Shape where
  constructor MkShape
  offsets : List (Int, Int)

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

allFins : Vect BoardSize (Fin BoardSize)
allFins = tabulate id

data OffsetValid : Board -> (baseR, baseC : Int) -> (offset : (Int, Int)) -> Type where
  MkOffsetValid : {baseR, baseC : Int} -> {offR, offC : Int} ->
                  (resR : Fin BoardSize) -> 
                  (resC : Fin BoardSize) -> 
                  (IsEmpty board resR resC) -> 
                  (the Integer (cast (finToNat resR)) = cast baseR + cast offR) ->
                  (the Integer (cast (finToNat resC)) = cast baseC + cast offC) ->
                  OffsetValid board baseR baseC (offR, offC)

data ValidPlacement : Board -> (br, bc : Int) -> Shape -> Type where
  NoMore  : {board : Board} -> {br, bc : Int} -> 
            ValidPlacement board br bc (MkShape [])

  NextPos : {board : Board} -> {br, bc : Int} -> {rest : List (Int, Int)} ->
            {offR, offC : Int} ->
            OffsetValid board br bc (offR, offC) ->
            ValidPlacement board br bc (MkShape rest) ->
            ValidPlacement board br bc (MkShape ((offR, offC) :: rest))

applyPlacement : Board -> ValidPlacement board br bc s -> Board
applyPlacement board NoMore = board
applyPlacement board (NextPos (MkOffsetValid r c _ _ _) rest) = 
  let nextBoard = placeBlock board r c
  in applyPlacement nextBoard rest

integerToFinWithProof : (n : Integer) -> (m : Nat) -> 
                        Maybe (f : Fin m ** cast (finToNat f) = n)
integerToFinWithProof n m = case integerToFin n m of
  Just f => case decEq (the Integer (cast (finToNat f))) n of
    Yes prf => Just (f ** prf)
    No _    => Nothing
  Nothing => Nothing

applyShape : (board : Board) -> (br, bc : Int) -> (s : Shape) -> ValidPlacement board br bc s -> Board
applyShape board br bc s prf = applyPlacement board prf

checkWithProof : (base : Int) -> (off : Int) -> 
                 Maybe (res : Fin BoardSize ** cast (finToNat res) = (the Integer (cast base)) + (the Integer (cast off)))
checkWithProof base off = 
  integerToFinWithProof (cast base + cast off) BoardSize

canPlaceAt : (board : Board) -> (br, bc : Int) -> (s : Shape) -> Maybe (ValidPlacement board br bc s)
canPlaceAt board br bc (MkShape []) = Just NoMore
canPlaceAt board br bc (MkShape ((offR, offC) :: rest)) = do
  (resR ** proofR) <- checkWithProof br offR
  (resC ** proofC) <- checkWithProof bc offC
  
  case checkCell board resR resC of
    Yes emptyPrf => do
      later <- canPlaceAt board br bc (MkShape rest)
      Just (NextPos (MkOffsetValid resR resC emptyPrf proofR proofC) later)
    No _ => Nothing

AnyMove : Board -> List Shape -> Type
AnyMove board hand = 
  (s : Shape ** (r : Fin BoardSize ** (c : Fin BoardSize ** (Elem s hand, ValidPlacement board (cast (finToNat r)) (cast (finToNat c)) s))))

findFit : (board : Board) -> (s : Shape) -> Maybe (r : Fin BoardSize ** c : Fin BoardSize ** ValidPlacement board (cast (finToNat r)) (cast (finToNat c)) s)
findFit board s = searchRows allFins
  where
    searchCols : Fin BoardSize -> Vect n (Fin BoardSize) -> Maybe (r : Fin BoardSize ** c : Fin BoardSize ** ValidPlacement board (cast (finToNat r)) (cast (finToNat c)) s)
    searchCols r [] = Nothing
    searchCols r (c :: cs) = 
      case canPlaceAt board (cast (finToNat r)) (cast (finToNat c)) s of
        Just prf => Just (r ** c ** prf)
        Nothing  => searchCols r cs

    searchRows : Vect m (Fin BoardSize) -> Maybe (r : Fin BoardSize ** c : Fin BoardSize ** ValidPlacement board (cast (finToNat r)) (cast (finToNat c)) s)
    searchRows [] = Nothing
    searchRows (r :: rs) = 
      case searchCols r allFins of
        Just result => Just result
        Nothing     => searchRows rs

anyMovesPossible : (board : Board) -> (hand : List Shape) -> Maybe (AnyMove board hand)
anyMovesPossible board [] = Nothing
anyMovesPossible board (s :: ss) = 
  case findFit board s of
    Just (r ** c ** prf) => Just (s ** r ** c ** (Here, prf))
    Nothing => case anyMovesPossible board ss of
      Just (s' ** r ** c ** (idx, prf)) => Just (s' ** r ** c ** (There idx, prf))
      Nothing => Nothing

zipVect : Vect BoardSize Bool -> Vect BoardSize (Fin BoardSize, Bool)
zipVect xs = zip allFins xs

replaceFalse : Fin BoardSize -> Vect BoardSize (Fin BoardSize, Bool) -> Vect BoardSize (Fin BoardSize, Bool)
replaceFalse x xs = map (\(i, b) => if i == x
                      then (i, False) else (i, b)) xs

unzipVect : Vect BoardSize (Fin BoardSize, Bool) -> Vect BoardSize Bool
unzipVect xs = map (\(i, b) => b) xs

data RowStatus2 : Vect n Bool -> Type where
  Full2    : RowStatus2 (replicate n True)
  AlmostFull2 : (ind : Fin BoardSize) -> RowStatus2 (unzipVect (replaceFalse ind (zipVect (replicate BoardSize True))))
  NotFull2 : (row : Vect n Bool) -> RowStatus2 row

data RowStatus : Vect n Bool -> Type where
  Full    : RowStatus (replicate n True)
  NotFull : (row : Vect n Bool) -> RowStatus row

inspectRow : (v : Vect BoardSize Bool) -> RowStatus v
inspectRow v with (decEq v (replicate BoardSize True))
  inspectRow (replicate BoardSize True) | (Yes Refl) = Full
  inspectRow v | (No _) = NotFull v

isRowFull : Vect BoardSize Bool -> Bool
isRowFull row with (inspectRow row)
  isRowFull _ | Full = True
  isRowFull _ | NotFull _ = False

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

makeMove : Board -> (br, bc : Int) -> Shape -> Either Board Board
makeMove board br bc shape with (canPlaceAt board br bc shape)
  makeMove board br bc shape | Just prf = 
    let placedBoard = applyShape board br bc shape prf
        blastedBoard = clearFullRows placedBoard
    in Right blastedBoard
  makeMove board br bc shape | Nothing = 
    Left board

hasValidMove : Board -> Shape -> Bool
hasValidMove board shape = 
  any (\r => any (\c => 
    isJust (canPlaceAt board (cast (finToNat r)) (cast (finToNat c)) shape)
  ) allFins) allFins

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

Show Shape where
  show (MkShape []) = "Empty Shape"
  show (MkShape offsets@((r, c) :: rest)) = 
    let
        rs = map fst offsets
        cs = map snd offsets
        minR = foldl min r rs
        maxR = foldl max r rs
        minC = foldl min c cs
        maxC = foldl max c cs
        
        rowRange = [minR .. maxR]
        colRange = [minC .. maxC]
        
        isPart : Int -> Int -> Bool
        isPart r' c' = any (\(or, oc) => or == r' && oc == c') offsets
        
        renderRow : Int -> String
        renderRow r' = (fastConcat $ map (\c' => if isPart r' c' then "■ " else "· ") colRange)
        
    in "\n" ++ (unlines $ map renderRow rowRange)

record GameState where
  constructor MkGameState
  board : Board
  hand  : List Shape

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
  let (currentHand, nextStream) = if null hand 
                                  then (Prelude.take 3 rest, drop 3 rest) 
                                  else (hand, rest) 
  
  putStrLn (show @{GameView} b) 
  putStrLn "Your Hand:"
  let handDisplay = zipWith (\i, s => show i ++ ":" ++ show s) [0..(length currentHand)] currentHand 
  putStrLn (unlines handDisplay) 

  case anyMovesPossible b currentHand of
    Nothing => do
      putStrLn "!!! GAME OVER !!! No more moves possible with the remaining hand." 
      putStrLn "Restarting game..."
      gameLoop tank (MkGameState emptyBoard []) nextStream 
    Just (s ** r ** c ** (proofInHand, placementPrf)) => do
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
          putStrLn "Error: Use format '0 3 3'" 
          gameLoop tank (MkGameState b currentHand) nextStream

covering
main : IO ()
main = do
  let shapes = randomShapes seedStream shapePool
  gameLoop forever (MkGameState emptyBoard []) shapes


isFull2 : Vect BoardSize Bool -> Bool 
