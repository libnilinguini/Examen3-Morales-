{-# LANGUAGE GADTs #-}
--   Generalised Algebraic Data Structures (GADTs)
module NPDAe
    (NPDAe(..), DeltaNPDAe, NPDAeStrInt, PDAconfig, Input, Stack
    , acceptFinalState
    , initConfig
    , nextConfigLsequence
    , showNPDAe, showDeltaNPDA
    , checkNPDAe
    , pdaStepK, pdaKsteps, pda1Step
    , nextConfigList, lfpOFpdaStepsOp
    , lastConfigINnextSequence
    )
-- 2025m03d27
-- Automatas de Pila No-Deterministas con transiciones epsilon, No-deterministic Pushdown automata (NPDAe)
-- mcb
--
where
import Data.Set as S  -- Finite Sets
    (Set, fromList, toList
    , singleton
    , member, isSubsetOf
    --, empty, union
    , unions
    , null)
    -- insert, intersection, powerSet) 
import Data.List as L
    (union) -- , nub)
--
-- import Word (PalabraAlf(..), toSigList, fromSigList) -- PalabraChr, concatWords
-- import Language (starKleeneK) -- ,concatLn
-- import NFA(NFAstateSym(..), fDeltaGorro)
--
-----------------------------------------------------------------------------------------
--
-- Automatas de Pila No-Deterministas, NPDAe (Non-Deterministic Finite Automata): -------
--
-- NPDAe con parametros para estados y simbolos: -----------------------------------------
-- DEFINITION 2.13 [Sipser-2013, p.113]
-- A pushdown automaton is a 6-tuple (Q,Σ,Γ,δ,q_0,F), 
-- where: 
--      0.  Q, Σ, Γ, and F are all ﬁnite sets,
--      0.mcb Q, Σ, and Γ are non-empty sets,
--      1. Q is the set of states,
--      2. Σ is the input alphabet,
--      3. Γ is the stack alphabet,
--      4. δ : Q × Σ_ε × Γ_ε --> P(Q × Γ_ε) is the transition function,
--      4.mcb δ: (Q × Γ_ε) × Σ_ε --> P(Q × Γ_ε) is the transition function,
--      5. q_0 ∈ Q is the start state, and
--      5.mcb S ⊆ Q the set of start states, and
--      6. F ⊆ Q is the set of accept states.

-- Transition functions for NPDAe: 
-- 4.mcb Delta: (Q x Sigma_e x Gamma_e) -> 2^(Q × Gamma_e), transition function.
type DeltaNPDAe state inputSym stackSym -- Delta:(Q x Sigma_e x Gamma_e) -> 2^(Q × Gamma_e). 
    = (state,inputSym,stackSym) -> (S.Set (state,stackSym))

showDeltaNPDA :: (Show state, Eq state, Show inputSym, Show stackSym, Eq stackSym) =>
                       NPDAe state inputSym stackSym -> String
-- Muestra la función de transición, xDelta, de un automata de pila (NPDAe)
showDeltaNPDA (NPDAe (xQ,xSigma,xGamma,eI,eZ,xDelta,_,_)) 
    = "QxSigmaExGammaE -> 2^(Q×GammaE), "
        ++ "\n\t\t where pairs ((p,sS,sG), Delta(p,sS,sG)) are: "
        ++ "\n\t\t {" ++ deltaStr ++ " }"
    where
    stateL      = S.toList xQ
    sigmaE      = eI : (S.toList xSigma)
    gammaE      = eZ : (S.toList xGamma)
    xDnoEmpty   = filter (\(_,xDpsz)-> xDpsz /= []) 
                    [((p,i,z), S.toList $ xDelta (p,i,z)) | 
                        p<-stateL, i <- sigmaE, z <- gammaE]
    deltaStr = concat ( ["\n\t\t  " ++ showPair (psz,xDpsz) | (psz,xDpsz) <- xDnoEmpty] 
                        ++ ["\n\t\t  ((otherwise), [])"])
    showPair (x,y) = show "(" ++ show x ++ show ", " ++ show y ++ show ")"
    
data NPDAe state inputSym stackSym -- Lo usual: state=String, inputSym=stackSym= Char
    = NPDAe -- Una tupla para M = (xQ,xS,xG,eI,eZ,xD,xI,xF)
        ( S.Set state                           -- 1. Q, conjunto de estados
        , S.Set inputSym                        -- 2. Sigma, conjunto de input symbols
        , S.Set stackSym                        -- 3. Gamma, conjunto de stack symbols
        , inputSym                              -- 3b.mcb epsilon: inputSym notIn Sigma
        , stackSym                              -- 3b.mcb epsilon: inputSym notIn Gamma
        , DeltaNPDAe state inputSym stackSym    -- 4.mcb Delta:(Q x Sigma_e x Gamma_e) -> 2^(Q × Gamma_e)
        , state                                 -- 5. The start state: xI in Q
        , S.Set state                           -- 6. The subseteq of accept states: xF subsetOf xQ
        ) 

checkNPDAe :: (Ord state, Ord inputSym, Ord stackSym) => 
    (NPDAe state inputSym stackSym) -> Bool
checkNPDAe (NPDAe  -- M = (xQ,xSigma,xGamma,eI,eZ,xDelta,xI,xF)
                    ( xQ        -- 1. conjunto de estados, Q
                    , xSigma    -- 2. set of input symbols, Sigma
                    , xGamma    -- 3. set of stack symbols, Gamma
                    , eI        -- 3b.mcb epsilon: inputSym notIn Sigma
                    , eZ        -- 3c.mcb epsilon: stackSym notIn Gamma
                    , xDelta    -- 4.mcb Delta: (Q x Sigma_e x Gamma_e) -> 2^(Q × Gamma_e)
                    , xI        -- 5. The start state: xI in Q
                    , xF        -- 6. The subseteq of accept states: xF subsetOf xQ
                    ) )
    =      (not (S.null xQ))                -- xQ /= []
        && (not (S.null xSigma))            -- xSigma /= []
        && (not (S.null xGamma))            -- xGamma /= []
        && (not (S.member eI xSigma))       -- eI notIn xSigma
        && (not (S.member eZ xGamma))       -- eZ notIn xGamma
        && (S.member xI xQ)                 -- xI in xQ
        && (S.isSubsetOf xF xQ)             -- xF isSubsetOf xQ
        && and [                            -- forAll psz in Dom(Delta):
                (xDelta psz)                --      Delta (psz) 
                `S.isSubsetOf`              --      isSubsetOf 
                xQL_x_GammaE                --      Q x Gamma_e
                    | psz <- xDeltaDomain] 
    where
    xQL    = S.toList xQ
    sigmaE = eI : (S.toList xSigma)
    gammaE = eZ : (S.toList xGamma)
    xDeltaDomain = [(q,s,z) | q<-xQL, s<-sigmaE, z<-gammaE] -- Dom(Delta)= QxSigmaExGammaE
    xQL_x_GammaE = S.fromList [(q,z) | q<-xQL, z<-gammaE]   -- QxGammaE

--
-- CONVIENE definir una funcion constructora de NPDAe válidos
-- cNPDAe   -- Una tupla para M = (xQ,xS,xG,eI,eZ,xD,xI,xF)
--         ( S.Set state                           -- 1. Q, conjunto de estados
--         , S.Set inputSym                        -- 2. Sigma, conjunto de input symbols
--         , S.Set stackSym                        -- 3. Gamma, conjunto de stack symbols
--         , inputSym                              -- 3b.mcb epsilon: inputSym notIn Sigma
--         , stackSym                              -- 3b.mcb epsilon: inputSym notIn Gamma
--         , DeltaNPDAe state inputSym stackSym    -- 4.mcb Delta: (Q x Sigma_e x Gamma_e) -> 2^(Q × Gamma_e)
--         , state                                 -- 5. The start state
--         , S.Set state                           -- 6. The set of accept states
--         ) =  

-- NPDAe donde los estados son strings, y los simbolos de entrada y de la pila son enteros: 
type NPDAeStrInt = NPDAe String Int Int -- NPDAe state=String inputSym=Int stackSym=Int
--
-- Una instancia de Show para mostrar NPDAe generales, NPDAe state inputSym:
instance (Show state, Eq state, Ord state, Show inputSym, Ord inputSym, Show stackSym, Eq stackSym, Ord stackSym) => 
            Show (NPDAe state inputSym stackSym) where
    show = showNPDAe
--
showNPDAe :: (Show state, Eq state, Ord state, Show inputSym, Ord inputSym, Show stackSym, Eq stackSym, Ord stackSym)=>  
        (NPDAe state inputSym stackSym) -> String
showNPDAe m@(NPDAe  -- M = (xQ,xSigma,xGamma,eI,eZ,xDelta,xI,xF)
                    ( xQ        -- 1. conjunto de estados, Q
                    , xSigma    -- 2. set of input symbols, Sigma
                    , xGamma    -- 3. set of stack symbols, Gamma
                    , eI        -- 3b.mcb epsilon: inputSym notIn Sigma
                    , eZ        -- 3c.mcb epsilon: stackSym notIn Gamma
                    , _         -- 4.mcb Delta: (QxSigmaExGammaE) -> 2^(Q×GammaE)
                    , xI        -- 5.mcb set of start states
                    , xF        -- 6.mcb set of accept states
                    ) )
    = case (checkNPDAe m) of
        False   -> error $ "\n showNPDAe: This automata is NOT a valid NPDAe.\n"
        True    -> "NPDAe (" ++ " -- This automata NPDAe IS valid.\n"
                        ++ "\t Q= "             ++ stateStr 
                        ++ ",\n\t Sigma= "      ++ sigmaStr 
                        ++ ",\n\t Gamma= "      ++ gammaStr 
                        ++ ",\n\t epsilonI= "   ++ eIstr
                        ++ ",\n\t epsilonZ= "   ++ eZstr
                        ++ ",\n\t Delta: "      ++ deltaStr
                        ++ ",\n\t I="           ++ q0Str 
                        ++ ",\n\t F="           ++ xFstr 
                        ++ ")"
                where
                stateStr = show (S.toList xQ)
                sigmaStr = show (S.toList xSigma)
                gammaStr = show (S.toList xGamma)
                eIstr    = show eI
                eZstr    = show eZ
                deltaStr = showDeltaNPDA m
                q0Str    = show xI
                xFstr    = show [p | p <- (S.toList xF)]
                --
    
--
--
-- Tests: VER TestNFAe.hs

-----------------------------------------------------------------------------------------
-- Configuraciones

type Input sym = [sym]
    -- Un input es una lista, w, de símbolos de entrada (Sigma)
    -- El input, w, se consume de izquierda a derecha,
    -- si el input es x:w', 
    -- entonces, después de consumir un símbolo, el input será w'.

type Stack sym = [sym]  
    -- Un stack es una lista, s, de símbolos de la pila (Gamma)
    -- Un push del símbolo z en el stack s
    -- se realiza agregando z al inicio de s, z:s.
    -- Si el stack es z:s', un pop(z:s') produce el stack s'.

type PDAconfig state inputSym stackSym = (state, Input inputSym, Stack stackSym)
    -- (q,w,z): PDAconfig state inputSym stackSym
    --          q: edoActual
    --          w: lo que resta del input (input no-leido), w es una lista de inputSym
    --          z: contenido actual de la pila, una lista de stackSym.

initConfig :: (NPDAe state inputSym stackSym) -> (Input inputSym) -> (state, (Input inputSym), (Stack stackSym))
-- Configuracion inicial.
initConfig (NPDAe (_,_,_,_,_,_,xI,_)) w = (xI,w,emptyStack)
    where emptyStack = []
    
-- Significado de las aristas en diagramas de NPDAs (Sipser):
--
-- La  arista 
--  q2  ---->(1, 0-->e)  q3
-- representa:
--      delta(q2,1, 0)={(q3,e)}.
-- Estando en q2,
-- consumiendo input=1,
-- hacer un pop(0), y pasar a q3 (0-->e).
-- 
-- El segundo componente, 0-->e, de  la etiqueta de la arista
-- ---->(1, 0-->e)
-- representa
-- pop(0)
-- Es decir:
-- reemplazar el tope de la pila(0),
-- por epsilon.
    
pda1Step :: (Ord state, Ord inputSym, Ord stackSym) =>
    NPDAe state inputSym stackSym -> (PDAconfig state inputSym stackSym) 
            -> Set (PDAconfig state inputSym stackSym)
-- Given an (NPDAe m@(xQ,xS,xG,eI,eZ,xDelta,xI,xF)) and a (PDAconfig (p,w,stack)),
-- use m to compute the set of next configurations for the current congiguration (p,w,stack).
pda1Step (NPDAe (_,_,_,eI,eZ,xDelta,_,_)) (p,w,stack) 
-- Apply m to get, from the current congiguration (p,w,stack), the list of next-configurations.
    = S.fromList (
            [(q,w,     push z stack)   | (q,z) <- xDp_eI_eZ]    -- xD(p,eI,eZ)=(q,z) ~ (eI,eZ->z)
        ++  [(q,w,     push z popStck) | (q,z) <- xDp_eI_xZ]    -- xD(p,eI,xZ)=(q,z) ~ (eI,xZ->z)
        ++  [(q,wTail, push z stack)   | (q,z) <- xDp_iI_eZ]    -- xD(p,iI,eZ)=(q,z) ~ (iI,eZ->z)
        ++  [(q,wTail, push z popStck) | (q,z) <- xDp_iI_xZ]    -- xD(p,iI,xZ)=(q,z) ~ (iI,xZ->z)
        )
    where
    push x stck = if (x==eZ) then stck else (x:stck)
    pop stck    = if stck /= [] then tail stck else []
    popStck     = pop stack
    readInput iw= if iw /= [] then (tail iw) else []
    wTail       = readInput w
    --
    xDp_eI_eZ   = S.toList (xDelta (p,eI,eZ))
    xDp_eI_xZ   = case stack of 
                    x:_ -> S.toList (xDelta (p,eI,x))
                    []  -> xDp_eI_eZ
    xDp_iI_eZ   = case w of 
                    i:_ -> S.toList (xDelta (p,i,eZ))
                    []  -> xDp_eI_eZ
    xDp_iI_xZ   = case (w,stack) of 
                    (i:_, x:_)  -> S.toList (xDelta (p,i,x))
                    ([],  _:_)  -> xDp_eI_xZ
                    (_:_,  [])  -> xDp_iI_eZ
                    ([],   [])  -> xDp_eI_eZ


pdaKsteps :: (Ord state, Ord inputSym, Ord stackSym) =>
    (NPDAe state inputSym stackSym) -> Int -> (PDAconfig state inputSym stackSym) 
                    -> Set (PDAconfig state inputSym stackSym)
pdaKsteps pda k config 
    | k >  0    = S.unions [pda1Step pda qzw  | qzw <- kMinus1stepsL]
    | k == 0    = S.singleton config
    | otherwise = error $
                    "pdaKsteps: wrong parameters, e.g. number of steps, k, should be >= 0, k= "
                    ++ show k
    where
    kMinus1stepsL = S.toList $ pdaKsteps pda (k-1) config 

pdaStepK :: (Ord state, Ord inputSym, Ord stackSym) =>
    (NPDAe state inputSym stackSym) -> (Input inputSym) -> Int 
        -> Set (PDAconfig state inputSym stackSym)
pdaStepK pda w k = pdaKsteps pda k (initConfig pda w)

nextConfigList :: (Ord state, Ord inputSym, Ord stackSym) =>
    (NPDAe state inputSym stackSym) 
        -> [(PDAconfig state inputSym stackSym)] -> [(PDAconfig state inputSym stackSym)]
nextConfigList pda configL
    = case configL of
            c:cnfgL     -> (S.toList (pda1Step pda c)) `L.union` nextConfigList pda cnfgL
            []          -> []

-- nextConfigLsequence :: (Ord state, Ord inputSym, Ord stackSym) =>
--     (NPDAe state inputSym stackSym) 
--             -> [PDAconfig state inputSym stackSym] -> [PDAconfig state inputSym stackSym]
-- -- Sequence of next-configurations.
-- nextConfigLsequence m currentConfigList 
--     = if nextConfigList_m_currentConfigList == currentConfigList
--          then currentConfigList
--          else    currentConfigList 
--               ++ nextConfigLsequence m nextConfigList_m_currentConfigList
--     where
--     nextConfigList_m_currentConfigList = (nextConfigList m) currentConfigList 
--             
-- nextConfigLsequence :: (Ord state, Ord inputSym, Ord stackSym) =>
--     (NPDAe state inputSym stackSym) 
--             -> [PDAconfig state inputSym stackSym] -> [PDAconfig state inputSym stackSym]
nextConfigLsequence :: (Ord state, Ord inputSym, Ord stackSym) =>
    (NPDAe state inputSym stackSym) -> 
        [[PDAconfig state inputSym stackSym]] -> [[PDAconfig state inputSym stackSym]]
-- Sequence of next-configurations.
nextConfigLsequence m currentConfigLsequence
    = if nextCnfgListOFlastCnfgList == lastCnfgList
         then currentConfigLsequence
         else nextConfigLsequence m updatedConfigLsequence
    where
    lastCnfgList                = last currentConfigLsequence
    nextCnfgListOFlastCnfgList  = (nextConfigList m) lastCnfgList
    updatedConfigLsequence      = currentConfigLsequence ++ [nextCnfgListOFlastCnfgList]
            
lastConfigINnextSequence :: (Ord state, Ord inputSym,Ord stackSym) =>
    NPDAe state inputSym stackSym -> 
        [PDAconfig state inputSym stackSym] -> [PDAconfig state inputSym stackSym]
-- Last config list in the sequence of next-configurations.
lastConfigINnextSequence m currentConfigList
    = if    (nextCnfgListOFcurrentCnfgList == [])
         || (nextCnfgListOFcurrentCnfgList == currentConfigList)
         then currentConfigList
         else lastConfigINnextSequence m nextCnfgListOFcurrentCnfgList
    where
    nextCnfgListOFcurrentCnfgList  = (nextConfigList m) currentConfigList
            

-- Def.[Hopcroft-Ullman p.112] Languages Accepted by an automata M in NPDAe.
-- Let  M=(Q,Sigma,Gamma,eI,eZ,Delta,I,F) in NPDAe.
--     1. We define L(M), the language accepted by final state, to be
--         L(M) := {w in Sigma* | (I,w,"") |-* (p,"",sZ) for some p in F and sZ in Gamma*}.   
--     2. We define N(M), the language accepted by empty stack (or null stack) to be
--         N(M) := {w in Sigma* | (I,w,"") |-* (p,"","") for some p in Q}.
--     When acceptance is by empty stack, the set of final states is irrelevant, 
--     and, in this case, we usually let the set of final states be the empty set.

-- Ejercicio. Sean m=(Q,Sigma,Gamma,eI,eZ,Delta,I,F) in NPDAe, y w in Sigma*.
--     1. Definir una función acceptFinalState tal que:
--         acceptFinalState m w = True sii w in L(m)  [Ver L(M) en la def. anterior]
--     2. Definir una función aceptaEmptyStack tal que:
--         aceptaEmptyStack m w = True sii w in N(m)  [Ver N(M) en la def. anterior]

------------------------------------------------------------------------------------
-- Def.[Similar a Hopcroft-Ullman p.112] Languages Accepted, in at most k steps, by an automata M in NPDAe.
-- Let  M=(Q,Sigma,Gamma,eI,eZ,Delta,I,F) in NPDAe.
--     1. We define L(M), the language accepted, in at most k steps, by final state, to be
--         L_k(M) := {w in Sigma^* | (I,w,"") |-^k (p,"",sZ) for some p in F and sZ in Gamma*}.   
--     2. We define N(M), the language accepted, in at most k steps, by empty stack (or null stack) to be
--         N_k(M) := {w in Sigma* | (I,w,"") |-^k (p,"","") for some p in Q}.

-- Ejercicio. Sean m=(Q,Sigma,Gamma,eI,eZ,Delta,I,F) in NPDAe, y w in Sigma*.
--     1. Definir una función acceptFinalState tal que:
--         acceptFinalState k m w = True sii w in L_k(m)  [Ver L_k(M) en la def. anterior]
--     2. Definir una función aceptaEmptyStack tal que:
--         aceptaEmptyStack k m w = True sii w in N_k(m)  [Ver N_k(M) en la def. anterior]
        

-- acceptFinalState :: (Ord state, Ord inputSym, Ord stackSym) =>
--                           (NPDAe state inputSym stackSym) -> (Input inputSym) -> Bool
-- -- Given m@(NPDAe (mQ,mS,mG,eI,eZ,mDelta,mI,mF)) and w, ...
-- acceptFinalState m@(NPDAe (_,_,_,_,_,_,_,mF)) w 
--     = or [(p `S.member` mF) && (wI==[]) | (p,wI,_) <- lastCnfgList]
--       && ((nextConfigList m) lastCnfgList == []) 
--     where
--     lastCnfgList = lastConfigINnextSequence m [initConfig m w]

acceptFinalState :: (Ord state, Ord inputSym, Ord stackSym) =>
                          (NPDAe state inputSym stackSym) -> (Input inputSym) -> Bool
-- Given m@(NPDAe (mQ,mS,mG,eI,eZ,mDelta,mI,mF)) and w, ...
acceptFinalState m@(NPDAe (_,_,_,_,_,_,_,mF)) w 
    =   or [ (or [(p `S.member` mF) && (wI==[]) | (p,wI,_) <- mConfig]) | mConfig <- configSequenceOFm]
    where
    configSequenceOFm = nextConfigLsequence m [[initConfig m w]]
            


-----------------------------------------------------------------------------------------
            
fix :: Eq t => (t -> t) -> t -> t
-- A fixed-point combinator
fix f x = let x' = f x in 
              if x == x' 
                 then x 
                 else fix f x'
--

lfpOFpdaStepsOp :: (Ord state, Ord inputSym, Ord stackSym) =>
    NPDAe state inputSym stackSym
        -> [PDAconfig state inputSym stackSym] -> [PDAconfig state inputSym stackSym]
lfpOFpdaStepsOp pda = fix (nextConfigList pda) -- fixed point of (nextConfigList pda)



-----------------------------------------------------------------------------------------

--
-- Ejercicio. Escribir una funcion que, dado un automa M=(Q,Sigma,e,Delta,S,F), 
-- calcule la funcion fDeltaGorroE (hat{Delta}) para un automata M in NPDAe.
-- VER abajo fDeltaGorroE.

-- 
-- -- Ejercicio. Definir una función aceptaNFAe tal que:
-- --      dados un automata NPDAe m, y una palabra w,
-- --      aceptaNFAe m w = True sii m acepta a w.
-- aceptaNFAe :: (Eq state,Show state,Ord state,  Show inputSym,Ord inputSym, Ord stackSym) => 
--     (NPDAe state inputSym stackSym) -> (PalabraAlf inputSym)  -> Bool
-- -- Función de aceptación para un automata NPDAe, m=(xQ,xS,xG,eI,eZ,xDelta,xI,xF).
-- aceptaNFAe m@(NPDAe (_,_,_,_,eZ,_,sI,sF)) w   -- acepta_m(w) 
--     = (S.fromList fDGmsIwStates `S.intersection`sF) /= S.empty -- True sii $deltaGE_m(sI,w) \cap sF \neq \varnothing$
--     where
--     sI'                 = S.fromList [(i,eZ) | i <- S.toList sI]
--     (fDGmsIwStates, _)  = unzip (S.toList (fDeltaGorroE m sI' w))
    
-- Tests (en TestNFAe.hs):
-- *Prelude> :l TestNFAe.hs 
-- *TestNPDAe> aceptaNFAe mEjP27Kozen (fromSigList [1,1,0,1,0,0,1,0])
-- True
-- *TestNPDAe> aceptaNFAe mEjP27Kozen (fromSigList [1,1,0,0,0,0,1,0])
-- False
-- *TestNPDAe> 


--
--
-- USO:
-- $ ghci
-- GHCi, version 8.0.2: http://www.haskell.org/ghc/  :? for help
-- Prelude> :l TestNPDA.hs 
-- Ok, modules loaded: ...
-- *TestNPDAe> 
-- *TestNPDAe> -- Desplegar m1 in NPDAe:
-- *TestNPDAe> m1
--          ...
-- *TestNPDAe> 
-- *TestNPDAe> 
-- *TestNPDAe> :q
-- Leaving GHCi.
-- $
-- 
--
