module NTMm2 where

import NTM
import Tapes
import Data.Set as S

-- Definición de estados y símbolos
q0, q1, qA, qR :: String
q0 = "q0"
q1 = "q1"
qA = "qA"
qR = "qR"

a, b, c, sB :: Char
a = 'a'
b = 'b'
c = 'c'
sB = '_'

-- Función de transición
m2Delta :: (String, Char) -> S.Set (String, Char, Move)
m2Delta (q, s)
    | (q, s) == (q0, a)  = S.fromList [(q1, a, R)]  -- Leer 'a' inicial y moverse a la derecha
    | q == q1 && s == sB = S.empty  -- Cadena vacía después de 'a' (rechazar)
    | q == q1 && s == a  = S.fromList [(q1, a, R)]  -- Seguir leyendo 'a's
    | q == q1 && s == b  = S.fromList [(qA, b, S), (q1, b, R)]  -- Posible final con 'b'
    | q == q1 && s == c  = S.fromList [(qA, c, S), (q1, c, R)]  -- Posible final con 'c'
    | q == q1            = S.fromList [(q1, s, R)]  -- Otros símbolos (no debería haber)
    | q == qA            = S.empty  -- Estado de aceptación
    | q == qR            = S.empty  -- Estado de rechazo
    | otherwise          = S.fromList [(qR, s, S)]  -- Rechazar cualquier otra cosa

-- Definición de la NTM m2
m2NTM :: NTM String Char
m2NTM = NTM {
    states = S.fromList [q0, q1, qA, qR],
    inputAlphabet = S.fromList [a, b, c],
    tapeAlphabet = S.fromList [a, b, c, sB],
    blankSymbol = sB,
    transition = m2Delta,
    startState = q0,
    acceptState = qA,
    rejectState = qR
}