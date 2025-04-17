-- Security Games as PMFs

import Mathlib.Data.ZMod.Basic
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Cryptolib4.ToMathlib
import Cryptolib4.Uniform

noncomputable section

/- From Lupo:
  G1 = public key space, G2 = private key space,
  M = message space, C = ciphertext space
  A_state = type for state A1 passes to A2
-/
variable {G1 G2 M C A_state: Type} [DecidableEq M]
          (keygen : PMF (G1 × G2))
          (encrypt : G1 → M → PMF C)
          (decrypt : G2 → C → M)
          (A1 : G1 → PMF (M × M × A_state))
          (A2 : C → A_state → PMF (ZMod 2))

/- From Lupo:
  Executes the a public-key protocol defined by keygen,
  encrypt, and decrypt
-/

def enc_dec (m : M) : PMF (ZMod 2) :=
  do
    let k ← keygen
    let c ← encrypt k.1 m
    pure (if decrypt k.2 c = m then 1 else 0)

/-  From Lupo:
  A public-key encryption protocol is correct if decryption undoes
  encryption with probability 1
-/
def pke_correctness : Prop := ∀ (m : M), enc_dec keygen encrypt decrypt m = pure 1

/- From Lupo:
  The semantic security game.
  Returns 1 if the attacker A2 guesses the correct bit
-/
def SSG : PMF (ZMod 2):=
do
  let k ← keygen
  let m ← A1 k.1
  let b ← uniform_2
  let c ← encrypt k.1 (if b = 0 then m.1 else m.2.1)
  let b' ← A2 c m.2.2
  pure (1 + b + b')

-- From Lupo: SSG(A) denotes the event that A wins the semantic security game
local notation "Pr[SSG(A)]" => ((SSG keygen encrypt A1 A2) 1)

def pke_semantic_security (ε : ENNReal) : Prop := Pr[SSG(A)] - 1/2 ≤ ε
