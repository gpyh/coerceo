module Main

import HexGrid
import Utils
import Data.Fin

TilePos : Type
TilePos = HexDirection 

data FieldPos : Type where
  MkFieldPos : HexPos -> TilePos -> FieldPos

data Color = White | Black

negate : Color -> Color
negate White = Black
negate Black = White

data Piece : Color -> Type where
  MkPiece : (color : Color) -> Piece color

data Player : Color -> Type where
  MkPlayer : (color : Color) -> Player color
  
data Tile : Type where
  NotOnBoard : (owner : Maybe (Player color)) -> Tile
  OnBoard : (c : Maybe (Piece White)) ->
            (d : Maybe (Piece Black)) ->
            (e : Maybe (Piece White)) ->
            (f : Maybe (Piece Black)) ->
            (a : Maybe (Piece White)) ->
            (b : Maybe (Piece Black)) -> Tile

toTile : Bool -> Bool -> Bool -> Bool -> Bool -> Bool -> Tile
toTile c d e f a b = OnBoard (p c) (p d) (p e) (p f) (p a) (p b) where
  p : Bool -> Maybe (Piece color)
  p False = Nothing
  p True = Just (MkPiece color)

rotate : Tile -> Tile
rotate (OnBoard c d e f a b) = OnBoard a b c d e f
rotate t = t

pairedTiles : (friendly : Bool) -> (posFstTile : TilePos) -> Tile
pairedTiles fr C = toTile True False fr (not fr) False False
pairedTiles fr D = toTile False True False fr (not fr) False
pairedTiles fr e = rotate (pairedTiles fr ((succ^4) e))
        
Board : Type 
Board = HexGrid 2 Tile

emptyTile : Tile
emptyTile = OnBoard Nothing Nothing Nothing Nothing Nothing Nothing

laurentius : Board
laurentius = lfr _ where
  lfr : (n : Nat) -> HexChain (S n) Z Tile
  lfr n with (hexPosFromNat n)
    lfr Z | Origin = emptyTile::Nil
    lfr (S k) | (Pos (S (S ppr)) _ _) = emptyTile :: lfr k
    lfr (S k) | (Pos _ e t) = pairedTiles (t == FZ) (pred e) :: lfr k

emptyBoard : Board
emptyBoard = replicate _ emptyTile 

