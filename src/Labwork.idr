module Labwork

import Data.Vect
import Data.Fin
import Decidable.Equality

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

||| An extrinsic proof that a cell is currently False (Empty)
public export
data IsEmpty : (board : Board) -> (r : Fin BoardSize) -> (c : Fin BoardSize) -> Type where
  ItIsFree : (index c (index r board) = False) -> IsEmpty board r c

||| Contra-proof: If a cell is True, it cannot be IsEmpty
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
  checkCell board r c | True  = No (\(ItIsFree contraPrf) => 
                                     occupiedNotFree p (ItIsFree contraPrf))

--------------------------------------------------------------------------------
--- 4. BOARD UPDATES
--------------------------------------------------------------------------------

||| Updates a single cell to True.
public export
placeBlock : (board : Board) -> (r, c : Fin BoardSize) -> (prf : IsEmpty board r c) -> Board
placeBlock board r c prf = 
  let targetRow = index r board
      newRow    = replaceAt c True targetRow
  in replaceAt r newRow board

--------------------------------------------------------------------------------
--- 5. SHAPE LOGIC
--------------------------------------------------------------------------------

public export
record Shape where
  constructor MkShape
  offsets : List (Int, Int)

||| Inductive proof that a whole shape fits on the board
public export
data CanPlace : (board : Board) -> (baseR, baseC : Int) -> (coords : List (Int, Int)) -> Type where
  EmptyFits : CanPlace board br bc []
  BlockFits : {r, c : Int} -> 
              (resR : Fin BoardSize) -> (resC : Fin BoardSize) ->
              (prf : IsEmpty board resR resC) ->
              CanPlace board br bc rest ->
              CanPlace board br bc ((r, c) :: rest)

--------------------------------------------------------------------------------
--- 6. LINE CLEARING (THE BLAST)
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

||| Returns True if the row is full, False otherwise
isRowFull : Vect BoardSize Bool -> Bool
isRowFull row with (inspectRow row)
  isRowFull (replicate BoardSize True) | Full = True
  isRowFull row | (NotFull _) = False

||| Creates a mask of which indices are full (True = Clear this)
getClearMask : Board -> Vect BoardSize Bool
getClearMask board = map isRowFull board

||| Clears the board based on pre-calculated row and column masks
applyMasks : (rowMask : Vect BoardSize Bool) -> 
             (colMask : Vect BoardSize Bool) -> 
             Board -> Board
applyMasks rowMask colMask board = 
  tabulate (\r => 
    tabulate (\c => 
      let cellShouldClear = index r rowMask || index c colMask
      in if cellShouldClear then False else index c (index r board)
    )
  )

||| The "Full Blast": Decides what to clear, then does it all at once
public export
clearFullRows : Board -> Board
clearFullRows board = 
  let rowMask = getClearMask board
      colMask = getClearMask (transpose board)
  in applyMasks rowMask colMask board



testBoard : Board
testBoard = [
  [False, False, False, False, False, True, True, True],
  [False, False, False, False, False, True, True, True],
  [False, False, False, False, False, True, True, True],
  [True, True, True, True, True, True, True, True],
  [False, False, False, False, False, True, False, True],
  [False, False, False, False, False, True, False, True],
  [False, False, False, False, False, True, False, True],
  [False, False, False, False, False, True, True, True]
]
