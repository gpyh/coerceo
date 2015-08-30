module Main

import HexGrid
import Utils
import Data.Fin
import Data.Vect

--------------------
-- Bunch of types --
--------------------

PiecePos : Type
PiecePos = HexDirection 

data FieldPos : Type where
  MkFieldPos : HexPos -> PiecePos -> FieldPos

data Color = White | Black

negate : Color -> Color
negate White = Black
negate Black = White

data Piece : Color -> Type where
  MkPiece : (color : Color) -> Piece color

data Player : Color -> Type where
  MkPlayer : (color : Color) -> Player color
  
data Tile : Type where
  NotOnB : (owner : Maybe (Player color)) -> Tile
  OnB : Vect 3 (Maybe (Piece White)) ->
        Vect 3 (Maybe (Piece Black)) -> Tile

toColorIndex : PiecePos -> (Color, Fin 3)
toColorIndex A = (White, FS (FS FZ))
toColorIndex B = (Black, FS (FS FZ))
toColorIndex e with (toColorIndex ((succ^2) e))
  | MkPair color (FS index) = (color, weaken index)

Board : Type 
Board = HexGrid 2 Tile

------------------
-- Useful stuff --
------------------

pop : Fin n -> Vect n (Maybe a) -> (Vect n (Maybe a), Maybe a)
pop _ Nil = (Nil, Nothing)
pop FZ (x :: xs) = ((Nothing :: xs), x)
pop (FS k) (x :: xs) = let (ys, y) = pop k xs in (x :: ys, y)

push : a -> Fin n -> Vect n (Maybe a) -> Maybe (Vect n (Maybe a))
push _ _ Nil = Nothing
push y FZ (Nothing :: xs) = Just (Just y :: xs)
push _ FZ (x :: xs) = Nothing
push y (FS k) (x :: xs) = map ((::) x) (push y k xs)

----------------------------
-- Adding/Removing Pieces --
----------------------------

-- All the error handling is made with Maybe
-- Which is also used to identify presence/absence of a tile (aaargh !)
-- TODO: Implement proper exceptions

||| Removes a piece from a tile
||| Returns the updated tile and the removed piece
||| If there was no piece to remove, for any reason, the piece is Nothing
popPiece : PiecePos -> Tile -> (Tile, Maybe (Piece color))
popPiece _ (NotOnB o) = (NotOnB o, Nothing) 
popPiece e (OnB w b) with (toColorIndex e)
  popPiece {color = White} e (OnB w b) | MkPair White n =
    let (trio, piece) = pop n w in (OnB trio b, piece)
  popPiece {color = Black} e (OnB w b) | MkPair Black n =
    let (trio, piece) = pop n b in (OnB w trio, piece)


||| Adds a piece to a tile
||| Returns the update tile or Nothing if it was imposible to at the piece
||| (for any reason)
pushPiece : Piece color -> PiecePos -> Tile -> Maybe Tile
pushPiece _ _ (NotOnB _) = Nothing
pushPiece c pp (OnB w b) with (toColorIndex pp)
  pushPiece {color = White} c pp (OnB w b) | MkPair White n =
    liftA2 OnB (push c n w) (Just b)
  pushPiece {color = Black} c pp (OnB w b) | MkPair Black n =
    liftA2 OnB (Just w) (push c n b)
                       
mUpdateAt : (Alternative app) => (p : HexPos) -> (f : a -> app a) ->
      HexChain end beg a -> app (HexChain end beg a)
mUpdateAt p f Nil = empty
mUpdateAt p f (x::xs) = if p == endPos xs
                       then liftA2 (::) (f x) (pure xs)
                       else liftA2 (::) (pure x) (mUpdateAt p f xs)

removePiece : FieldPos -> Board -> Maybe Board 
removePiece (MkFieldPos tp pp) b = mUpdateAt tp rm b where
  rm : Tile -> Maybe Tile
  rm t with (toColorIndex pp)
    | MkPair color _ with (popPiece {color = color} pp t)
      | MkPair (NotOnB _) _ = Nothing
      | MkPair _ Nothing = Nothing
      | MkPair tile _ = Just tile 

addPiece : FieldPos -> Board -> Maybe Board
addPiece (MkFieldPos tp pp) b = mUpdateAt tp add b where
  add : Tile -> Maybe Tile
  add t with (toColorIndex pp)
    | MkPair color _ = pushPiece (MkPiece color) pp t

-- Moving

inter : HexDirection -> HexDirection -> Fin 6
inter x y = inter' Z x y where
  inter' : Nat -> HexDirection -> HexDirection -> Fin 6
  inter' acc x y = if x == y
                 then fromNat acc
                 else inter' (S acc) (succ x) y

move : HexDirection -> HexPos -> HexPos
move d Origin = Pos Z ((succ^2) d) FZ
move d (Pos Z e FZ) with (inter e d)
  | FZ = Pos Z (succ e) FZ
  | (FS FZ) = Origin
  | (FS (FS FZ)) = Pos Z ((succ^5) e) FZ
  | (FS (FS (FS FZ))) = Pos (S Z) ((succ^5) e) (FS FZ) 
  | (FS (FS (FS (FS FZ)))) = Pos (S Z) e FZ
  | (FS (FS (FS (FS (FS FZ))))) = Pos (S Z) e (FS FZ)
move d (Pos (S k) e FZ) with (inter e d)
  | FZ = Pos (S k) e (FS FZ)
  | (FS FZ) = Pos k e FZ
  | (FS (FS FZ)) = Pos (S k) ((succ^5) e) last
  | (FS (FS (FS FZ))) = Pos (S (S k)) ((succ^5) e) last
  | (FS (FS (FS (FS FZ)))) = Pos (S (S k)) e FZ
  | (FS (FS (FS (FS (FS FZ))))) = Pos (S (S k)) e (FS FZ)
  
adj : Nat -> HexPos -> List HexPos
adj n p = filter ring (map ((flip move) p) [A,B,C,D,E,F]) where
  ring Origin = True
  ring (Pos r _ _) = r < n

--------------------
-- Starting board --
--------------------

emptyBoard : Board
emptyBoard = replicate 19 emptyTile where
  emptyTile = OnB (Nothing :: Nothing :: Nothing :: Nil)
                  (Nothing :: Nothing :: Nothing :: Nil)

-- TODO: redo the Laurentius but with actions on an empty board

test : Maybe Board
test = do
  b <- addPiece (MkFieldPos Origin C) emptyBoard
  b <- removePiece (MkFieldPos Origin C) b
  return b
