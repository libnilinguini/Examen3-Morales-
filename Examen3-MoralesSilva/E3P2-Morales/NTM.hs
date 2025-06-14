-- {-# LANGUAGE GADTs #-}
--   Generalised Algebraic Data Structures (GADTs)
module NTM
-- Non-Non-Deterministic Turing Machines (NTM)
     ( NTM(..), DeltaNTM, Move(..)
     , NTMstrInt
     , checkNTM
     -----------
     , showNTM
     , showDeltaNTM
    )
-- Non-Deterministic Turing Machines (NTM)
-- mcb 2024ago
--
where
import Data.Set as S  -- Finite Sets
    (Set 
    , toList
    , member
    , isSubsetOf
    , empty
    , null
    )   -- ,fromList, singleton, insert, intersection, powerSet), union, unions
        -- , powerSet, notMember, cartesianProduct

--
import Data.List as L
        ((\\)) -- union
--
-- import Word
--     (PalabraAlf(..)
--     , fromSigList, toSigList) -- , concatWords
--
-- import Language
--     (starKleene)
--
-------------------------------------------------------------------------------
--
-- Maquinas de Turing Deterministas, NTM (Non-Non-Deterministic Finite Automata):
--
-------------------------------------------------------------------------------
--
-- Transition functions for NTM:
-- δ : Q×Γ -> Q×Γ×{L,R,S} is the transition function
--     Al principio, Sipser usa {L,R}, pero luego usa {L,R,S}.
data Move = L | R | S -- movimiento de la TM (Left, Right, Stay)
    deriving (Show,Eq,Ord)
    -- Al principio, Sipser usa {L,R}, pero luego usa {L,R,S}.
--
-- type DeltaNTM state tapeSym -- δ : Q×Γ -> Q×Γ×{L,R,S} is the transition function
--     = (state,tapeSym) -> (state,tapeSym,Move)
type DeltaNTM state tapeSym -- δ : Q×Γ -> powerSet(Q×Γ×{L,R,S}) transition function
    = (state,tapeSym) -> S.Set (state,tapeSym,Move)
    -- OBSERVACION. NO posible checar en Haskell que una funcion total.
    -- Para checar totalidad, es necesario:
    --  type DeltaNTM state tapeSym = S.Set ((state,tapeSym),(state,tapeSym,Move))

---------------------
-- showDeltaNTM :: (Eq state, Eq tapeSym, Show state, Show tapeSym, Ord state, Ord tapeSym) =>
--                       NTM state tapeSym -> String
-- -- Muestra la función de transición, xDelta, de una maquina de Turing (NTM (xQ,xS,xGamma,sB,xDelta,qInit,qA,qR))
-- showDeltaNTM (NTM (xQ,_,xGamma,_,xDelta,_,qAccept,qReject))
-- -- delta : (Q-{qAccept,qReject})×Gamma -> Q×Gamma×{L,R,S}
--     = "(Q-{qAccept,qReject})xGamma -> Q×GammaxMove, "
--         ++ "\n\t\t where pairs ((p,sG), Delta(p,sG)) are: "
--         ++ "\n\t\t {" ++ deltaStr ++ " }"
--     where
--     stateL      = S.toList xQ
--     --sigma      = (S.toList xSigma)
--     gamma       = (S.toList xGamma)
--     xDcoDomain  = S.powerSet (S.fromList [(p,z,m) | p<- stateL, z <- gamma, m <- [L,R,S]])
--     xDnoEmpty   = filter (\(_,xDpz)-> xDpz `elem` xDcoDomain )
--                     [((p,z), xDelta (p,z)) |
--                         p<-stateL L.\\ [qAccept, qReject], z <- gamma]
--     deltaStr = concat ( ["\n\t\t  " ++ showPair (pz,xDpz) | (pz,xDpz) <- xDnoEmpty]
--                         ++ ["\n\t\t  ((otherwise), Undefined)"])
--     showPair (x,y) = show "(" ++ show x ++ show ", " ++ show y ++ show ")"
--
showDeltaNTM :: (Eq state, Eq tapeSym, Show state, Show tapeSym, Ord state, Ord tapeSym) =>
                      NTM state tapeSym -> String
-- Muestra la función de transición, xDelta,
-- de una maquina de Turing (NTM (xQ,xS,xGamma,sB,xDelta,qInit,qA,qR))
showDeltaNTM (NTM (xQ,_,xGamma,_,xDelta,_,_,_))
-- delta : (Q-{qAccept,qReject})×Gamma -> Q×Gamma×{L,R,S}
    = "(Q-{qAccept,qReject})xGamma -> Q×GammaxMove, "
        ++ "\n\t\t where pairs ((p,sG), Delta(p,sG)) are: "
        ++ "\n\t\t {" ++ deltaStr ++ " }"
    where
    stateL      = S.toList xQ
    gamma       = (S.toList xGamma)
    paresNoEmpty = [((p,z), xDelta (p,z)) | p<-stateL, z <- gamma] \\ paresEmpty
    paresEmpty   = [((p,z),S.empty) | p<-stateL, z <- gamma]
    deltaStr     = concat (["\n\t\t  " ++ show (pz,xDpz) | (pz,xDpz) <- paresNoEmpty]
                          ++ ["\n\t\t  ((otherwise),fromList [])"])

---------------------
    
-- DEFINITION 3.3 [Sipser 3ed p.168]
-- A Turing machine is a 7-tuple, (Q,Σ,Γ,δ,q_0,q_accept, q_reject ), where
-- Q, Σ, Γ are all ﬁnite sets and
-- 1. Q is the set of states,
-- 2. Σ is the input alphabet not containing the blank symbol sB ,
-- 3. Γ is the tape alphabet, where sB ∈ Γ and Σ ⊆ Γ,
-- 3b. mcb sB:tapeSym, sB in Gamma-Sigma
-- 4. δ : Q × Γ->Q × Γ × {L, R} is the transition function,
-- 5. q_0 ∈ Q is the start state,
-- 6. q_accept ∈ Q is the accept state, and
-- 7. q_reject ∈ Q is the reject state, where q_reject /= q_accept .

data NTM state tapeSym -- Lo usual: state=String, tapeSym= Char
    = NTM -- Una tupla para M = (xQ,xS,xG,sB,xD,qInit,qAccept,qReject)
        ( S.Set state               -- 1. Q, conjunto de estados
        , S.Set tapeSym             -- 2. Sigma subsetOf Gamma, conjunto de input symbols
        , S.Set tapeSym             -- 3. Gamma, conjunto de tape symbols
        , tapeSym                   -- 3b.mcb sB:tapeSym, sB in Gamma-Sigma
        , DeltaNTM state tapeSym    -- 4. xD : Q×Γ -> powerSet(Q×Γ×{L,R,S})
        , state                     -- 5. The start state:  qInit in Q
        , state                     -- 6. The accept state: qAccept in Q
        , state                     -- 7. The reject state: qReject in Q
        ) 
        -- deriving (Eq)  -- ANTES modificar DeltaNTM a conjunto.

-- Una instancia de Show para mostrar NTM generales, NTM state inputSym:
instance
    (Show state, Ord state, Show tapeSym, Ord tapeSym) =>
            Show (NTM state tapeSym) where
    show = showNTM
--
showNTM :: (Show state, Eq state, Ord state, Show tapeSym, Eq tapeSym, Ord tapeSym)=>
        (NTM state tapeSym) -> String
showNTM m@(NTM      -- M = (mQ,mSigma,mGamma,sB,xD,qInit,qAccept,qReject)
        ( mQ        -- 1. Q, conjunto de estados
        , mSigma    -- 2. Sigma, conjunto de input symbols
        , mGamma    -- 3. Gamma, conjunto simbolos de la cinta.
        , sB        -- 3b.mcb blank space sB:tapeSym, sB in Gamma-Sigma
        , _         -- 4. xD : Q×Γ -> Q×Γ×{L,R,S} is the transition function
        , qInit     -- 5. The start state: qInit in Q
        , qAccept   -- 6. The accept state: qAccept in Q
        , qReject   -- 7. The reject state: qReject in Q
        ) )
    = 
    case (checkNTM m) of
        (False,errStr)  -> error $ "\n showNTM: This machine is NOT a valid NTM."
                                ++ "\n\t" ++ errStr
        (True,_)        -> -- error $ "\n showNTM: This machine IS a valid NTM\n"
                "NTM (" ++ " -- This Turing Machine (NTM) IS valid.\n"
                        ++ "\t Q= "             ++ stateStr 
                        ++ ",\n\t Sigma= "      ++ sigmaStr 
                        ++ ",\n\t Gamma= "      ++ gammaStr 
                        ++ ",\n\t BlankSym= "   ++ (show sB)
                        ++ ",\n\t Delta: "      ++ deltaStr
                        ++ ",\n\t qInit= "      ++ show qInit
                        ++ ",\n\t qAccept= "    ++ show qAccept 
                        ++ ",\n\t qReject= "    ++ show qReject 
                        ++ ")"
                where
                stateL   = (S.toList mQ)
                mSigmaL  = (S.toList mSigma)
                mGammaL  = (S.toList mGamma)
                sigmaStr = show mSigmaL
                gammaStr = show mGammaL
                stateStr = show stateL
                deltaStr = showDeltaNTM m
--

-- NTM donde los estados son strings, y los simbolos de entrada y de la pila son enteros:
type NTMstrInt = NTM String Int -- NTM state=String inputSym=tapeSym=Int

--
-- Tests: VER TestNTM.hs

-----------------------------------------------------------------------------
--

--
checkNTM :: (Show state, Ord state, Show tapeSym, Ord tapeSym) =>
        NTM state tapeSym -> (Bool,String)
checkNTM (NTM (xQ,xSigma,xGamma,sB,xDelta,qInit,qAccept,qReject))
    |   (S.null xQ)             = (False, "xQ = []")
    |   (S.null xSigma)         = (False, "xSigma = []")
    |   (S.null xGamma)         = (False, "xGamma = []")
    -----------------------------
    |   (    S.member sB xSigma)            = (False, "sB in xSigma")
    |   (not(S.member sB xGamma))           = (False, "sB notIn xGamma")
    |   (not(S.isSubsetOf xSigma xGamma))   = (False, "xSigma isNotSubsetOf xGamma")
    -----------------------------
    |   (not (S.member qInit xQ))   = (False, "qInit notIn xQ")
    |   (not (S.member qAccept xQ)) = (False, "qAccept notIn xQ")
    |   (not (S.member qReject xQ)) = (False, "qReject notIn xQ")
    |   (qReject == qAccept)        = (False, "qReject = qAccept")
    -----------------------------
    |   not deltaOFqAsIsEmpty   = (False, "exists s: Delta(qAccept,s) <> {}")
    |   not deltaOFqRsIsEmpty   = (False, "exists s: Delta(qReject,s) <> {}")
        -- OBSERVACION. NO posible checar en Haskell que una funcion total.
        -- Para checar totalidad, es necesario:
        --  type DeltaNTM state tapeSym = S.Set ((state,tapeSym),(state,tapeSym,Move))
    -----------------------------
    | otherwise                 = (True, "This machine is a valid NTM")
    -----------------------------
    where
    xGammaList          = S.toList xGamma
    deltaOFqAsIsEmpty   = and [xDelta(qAccept,s)== S.empty | s <- xGammaList]
    deltaOFqRsIsEmpty   = and [xDelta(qReject,s)== S.empty | s <- xGammaList]
--

--
--
----------------------------------------------------------------
-- --
-- -- CONVIENE definir una funcion constructora de NTM válidos
--     = NTM -- Una tupla para M = (xQ,xS,xG,sB,xD,qInit,qAccept,qReject)
--         ( S.Set state               -- 1. Q, conjunto de estados
--         , S.Set tapeSym             -- 2. Sigma subsetOf Gamma, conjunto de input symbols
--         , S.Set tapeSym             -- 3. Gamma, conjunto de tape symbols
--         , tapeSym                   -- 3b.mcb sB:tapeSym, sB in Gamma-Sigma
--         , DeltaNTM state tapeSym    -- 4. xD : Q×Γ -> Q×Γ×{L,R,S} is the transition function
--         , state                     -- 5. The start state:  qInit in Q
--         , state                     -- 6. The accept state: qAccept in Q
--         , state                     -- 7. The reject state: qReject in Q
--         )
--

-- 
-------------------------------------------------------------------------------
--
--
------------------------------------------------------------------------
-- Sipser:
--
-- Def. Un lenguaje L subconjunto de Sigma* es Turing-reconocible (r.e.)
-- sii existe una TM m tal que: L == lRecognizedByTM(m)
--
-- Def. Una máquina Turing m es Total sii m para con todos los inputs.
-- Es decir, m es total sii \forall w in \Sigma*: 
--                          (tmAccept m w) or (tmReject m w)
--
-- Def. Una máquina Turing m entra en Loop sii m no para con todos los inputs.
-- Es decir, m entra en Loop sii \exists w in \Sigma*: 
--                          not(tmAccept m w) and not (tmReject m w)
-- Obs: m es Total sii m NO entra en Loop
-- Obs: m entra en Loop sii m NO es Total
--
-- Def. Un lenguaje L subconjunto de Sigma* es Turing-decidible (recursivo)
-- sii existe una TM m tal que: m es Total y L == lRecognizedByTM(m)

--
-------------------------------------------------------------------------------
-- De Sipser:
--
-- We say that conﬁguration C1 yields conﬁguration C2 
-- if the Turing machine can legally go from C1 to C2 in a single step.
--
-- Here we formalize our intuitive understanding of the way that a Turing ma-
-- chine computes. Say that conﬁguration C 1 yields conﬁguration C 2 if the Turing
-- machine can legally go from C 1 to C 2 in a single step. We deﬁne this notion
-- formally as follows.
-- Suppose that we have a, b, and c in Γ, as well as u and v in Γ ∗ and states q i
-- and q j . In that case, ua q i bv and u q j acv are two conﬁgurations. Say that
-- ua q i bv
-- yields
-- u q j acv
-- if in the transition function δ(q i , b) = (q j , c, L). That handles the case where the
-- Turing machine moves leftward. For a rightward move, say that
-- ua q i bv
-- yields
-- uac q j v
-- if δ(q i , b) = (q j , c, R).
--    
-- 
-- Special cases occur when the head is at one of the ends of the conﬁguration.
-- For the left-hand end, the conﬁguration q i bv yields q j cv if the transition is left-
-- moving (because we prevent the machine from going off the left-hand end of the
-- tape), and it yields c q j v for the right-moving transition. For the right-hand end,
-- the conﬁguration ua q i is equivalent to ua q i � because we assume that blanks
-- follow the part of the tape represented in the conﬁguration. Thus we can handle
-- this case as before, with the head no longer at the right-hand end.
-- 


--
-- The start conﬁguration of M on input w is the conﬁguration q 0 w, which
-- indicates that the machine is in the start state q 0 with its head at the leftmost
-- position on the tape. In an accepting conﬁguration, the state of the conﬁguration
-- is q accept . In a rejecting conﬁguration, the state of the conﬁguration is q reject .
-- Accepting and rejecting conﬁgurations are halting conﬁgurations and do not
-- yield further conﬁgurations. Because the machine is deﬁned to halt when in the
-- states q accept and q reject , we equivalently could have deﬁned the transition function
-- to have the more complicated form δ : Q � × Γ−→ Q × Γ × {L, R}, where Q � is Q
-- without q accept and q reject . A Turing machine M accepts input w if a sequence of
-- conﬁgurations C 1 , C 2 , . . . , C k exists, where
-- 1. C 1 is the start conﬁguration of M on input w,
-- 2. each C i yields C i+1 , and
-- 3. C k is an accepting conﬁguration.
-- 
-- 
-- The collection of strings that M accepts is the language of M , or the lan-
-- guage recognized by M , denoted L(M ).
-- 
-- DEFINITION 3.5 [Language Turing-recognizable or Recursively enumerable (r.e.)]
-- Call a language Turing-recognizable if some Turing machine
-- recognizes it. 1
-- When we start a Turing machine on an input, three outcomes are possible.
-- The machine may accept, reject, or loop. By loop we mean that the machine simply
-- does not halt. Looping may entail any simple or complex behavior that never
-- leads to a halting state.
-- A Turing machine M can fail to accept an input by entering the q reject state
-- and rejecting, or by looping. Sometimes distinguishing a machine that is looping
-- from one that is merely taking a long time is difﬁcult. For this reason, we prefer
-- Turing machines that halt on all inputs; such machines never loop. These ma-
-- chines are called deciders because they always make a decision to accept or reject.
-- A decider that recognizes some language also is said to decide that language.
-- 
-- DEFINITION 3.6 [Language Turing-decidable or Recursive]]
-- Call a language Turing-decidable or simply decidable if some
-- Turing machine decides it. 2
-- Next, we give examples of decidable languages. Every decidable language
-- is Turing-recognizable. We present examples of languages that are Turing-
-- recognizable but not decidable after we develop a technique for proving un-
-- decidability in Chapter 4.
--
-------------------------------------------------------------------
--
