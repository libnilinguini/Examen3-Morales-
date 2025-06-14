{-# LANGUAGE GADTs #-}
--   Generalised Algebraic Data Structures (GADTs)
module Tapes
-- Tapes for executing Turing Machines
    ( Rtape
    , Ltape(..)
    , headRtape
    , tailRtape
    , toTapeSymList
    )
--
-- Tapes for executing Turing Machines
-- mcb 2024ago
--
where
--
-- import Data.Set as S  -- Finite Sets
--     (Set
--     , member
--     --, toList, fromList
--     --, singleton
--     --, isSubsetOf
--     --, empty, union, unions
--     --, null, insert, intersection, powerSet
--     )
--     -- )
--
-- import Data.List as L
--         ((\\)) -- union
--
-------------------------------------------------
-- import Word
--     (PalabraAlf(..)
--     , fromSigList, toSigList) -- , concatWords
-- import Language
--     (starKleene)
--
-------------------------------------------------------------------------------
-- Tapes para maquinas de Turing
-------------------------------------------------------------------------------
--

type Rtape tapeSym = [tapeSym]  -- Cinta a la derecha (Right) del estado actual.
                                -- add symbols to the left, s:tape.
                                -- bv = b:v, donde b:tapeSym y v:[tapeSym]
headRtape :: tapeSym -> (Rtape tapeSym) -> tapeSym
-- Given a blank symbol, sB, and a Rtape rT, return the first symbol of rT
-- We assume that: to the right of rT there are only blanks.
headRtape sB rT
    = case rT of
        s:_ -> s
        []  -> sB -- We assume that: to the right of rT there are only blanks.
--
tailRtape :: tapeSym -> (Rtape tapeSym) -> (Rtape tapeSym)
-- Given a blank symbol, sB, and a Rtape rT, return the first symbol of rT
-- We assume that: to the right of rT there are only blanks.
tailRtape sB rT
    = case rT of
        [_]   -> [sB] -- We assume that: to the right of rT there are only blanks.
        []    -> [sB] -- We assume that: to the right of rT there are only blanks.
        _:rT' -> rT'
--

--
data Ltape tapeSym = -- Cinta a la izquierda (Left) del estado actual.
      Lnull                         -- null left tape
    | Ladd (Ltape tapeSym) tapeSym  -- add symbols to the right, tape `Ladd` s.
    deriving (Eq,Ord)               -- ua = (Ladd u a), donde u:(Ltape tapeSym) y a:tapeSym
--
instance (Show tapeSym) =>
            Show (Ltape tapeSym) where
    show= showLtape
--
showLtape :: Show tapeSym => Ltape tapeSym -> String
showLtape tL = case tL of
                Ladd _ _    -> show (toTapeSymList tL)
                Lnull       -> emptyStr -- Init of tape
    where emptyStr = "\"\"" -- comillas comillas
--

--
-- Convierte una Ltape de simbolos sym, Ltape sym, a una lista de simbolos, [sym].
toTapeSymList :: Ltape sym -> [sym]
toTapeSymList leftTape =
    case leftTape of
        Ladd leftTapeX tapeSym  -> (toTapeSymList leftTapeX) ++ [tapeSym]
        Lnull                   -> []
--

--
