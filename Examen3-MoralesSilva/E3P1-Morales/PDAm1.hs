module PDAm1 where

import NPDAe

-- PDA que acepta únicamente las cadenas:
-- "abc", "aabbcc", "aaabbbccc"
-- Es decir: L = { a^n b^n c^n | 1 ≤ n ≤ 3 }

m1PDA :: NPDA Char Char Int
m1PDA = NPDA
  [0,1,2,3]             -- Conjunto de estados
  ['a','b','c']         -- Alfabeto de entrada
  ['Z','A']             -- Alfabeto de pila
  delta                 -- Función de transición
  0                     -- Estado inicial
  'Z'                   -- Símbolo inicial de pila
  [3]                   -- Estados de aceptación

transitions =
  [ ((0, Just 'a', 'Z'), (0, ['A', 'Z']))
  , ((0, Just 'a', 'A'), (0, ['A', 'A']))
  , ((0, Just 'b', 'A'), (1, []))  -- Desapila 'A' para 'b'
  , ((1, Just 'b', 'A'), (1, []))  -- Desapila 'A' para 'b' adicional
  , ((1, Just 'c', 'A'), (2, []))  -- Desapila 'A' para 'c'
  , ((2, Just 'c', 'A'), (2, []))  -- Desapila 'A' para 'c' adicional
  , ((2, Nothing, 'Z'), (3, ['Z']))  -- Acepta
  ]

main :: IO ()
main = do
  putStrLn "Resultados de aceptación:"
  putStrLn $ "'' (lambda): " ++ show (acceptFinalState m1PDA "")
  putStrLn $ "'abc': " ++ show (acceptFinalState m1PDA "abc")
  putStrLn $ "'aabbcc': " ++ show (acceptFinalState m1PDA "aabbcc")
  putStrLn $ "'aabbc': " ++ show (acceptFinalState m1PDA "aabbc")