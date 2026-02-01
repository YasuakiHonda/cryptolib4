import Mathlib.Data.BitVec
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Data.ZMod.Defs

variable (G : Type) [Fintype G] [Group G]

noncomputable section

instance (n : ℕ) : Fintype (BitVec n) := by
  apply Fintype.ofEquiv (Fin (2^n))
  refine (RingEquiv.toEquiv ?_).symm
  exact BitVec.equivFin

lemma card (n : ℕ) : Fintype.card (BitVec n) = 2^n := by
  calc
    Fintype.card (BitVec n)
    = Fintype.card (Fin (2^n)) := Fintype.card_congr (@BitVec.equivFin n)
    _= 2^n                  := Fintype.card_fin _

instance : ∀ (n : ℕ) [NeZero n], Group (ZMod n) := fun
  | .zero => Multiplicative.group
  | .succ _ => Multiplicative.group

def uniform_bitvec (n : ℕ) : PMF (BitVec n) := PMF.uniformOfFintype (BitVec n)
def uniform_group : PMF G := PMF.uniformOfFintype G
def uniform_zmod (n : ℕ) [NeZero n] : PMF (ZMod n) := uniform_group (ZMod n)
def uniform_2 : PMF (ZMod 2) := uniform_zmod 2


lemma uniform_bitvec_prob {n : ℕ} :
    ∀ (bv : BitVec n), (uniform_bitvec n) bv = 1/(2^n : ENNReal) := by
  intro bv
  simp only [one_div]
  simp only [uniform_bitvec]
  rw [PMF.uniformOfFintype_apply]
  rw [card n]
  norm_cast

lemma uniform_group_prob :
  ∀ (g : G), (uniform_group G) g = 1/((Fintype.card G):ENNReal) := by
  intro g
  simp only [one_div]
  simp only [uniform_group]
  exact PMF.uniformOfFintype_apply g

lemma uniform_zmod_prob {n : ℕ} [NeZero n] : ∀ (a : ZMod n), (uniform_zmod n) a = 1/n := by
  intro a
  simp only [uniform_zmod]
  rw [uniform_group_prob (ZMod n)]
  rw [ZMod.card n]

lemma uniform_2_prob : ∀ (a : ZMod 2), (uniform_2) a = 1/2 := by
  intro a
  simp only [uniform_2]
  rw [@uniform_zmod_prob 2]
  simp
