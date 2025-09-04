import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Order.Filter.Defs
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic
import Cryptolib4.Negligible_def


lemma zero_negl : negligible (λ _ => 0) := by
  intro c _
  let cr:NNReal := c
  use 1
  constructor
  · norm_num
  intro n hn
  norm_num
  apply pow_pos
  exact Nat.cast_pos'.mpr hn

lemma negl_add_negl_negl {f g : ℕ → ℝ} : negligible f → negligible g → negligible (f + g) := by
  intro hf hg
  rw [← neglK_eq_negl]
  rw [neglK_eq_neglK_ex]
  unfold negligibleK_ex
  use 2
  constructor
  · norm_num
  intro c hc

  rw [negligible] at hf
  rcases (hf c hc) with ⟨nf,hf⟩
  rw [negligible] at hg
  rcases (hg c hc) with ⟨ng,hg⟩

  let nfg := nf + ng
  have : ∀n, nfg ≤ n → abs ((f+g) n) < 2 / ↑n ^ c := by
    intro n nfg_n

    have nfg_f: abs (f n) < 1 / ↑n ^ c := by
      have nf_le_nfg: nf ≤ nfg := by exact Nat.le_add_right nf ng
      have nf_le_n : nf≤n := by linarith
      exact hf.2 n nf_le_n
    have nfg_g: abs (g n) < 1 / ↑n ^ c := by
      have ng_le_nfg: ng ≤ nfg := by exact Nat.le_add_left ng nf
      have ng_le_n : ng≤n := by linarith
      exact hg.2 n ng_le_n
    have : abs ((f+g) n) ≤ abs (f n) + abs (g n) := by
      have hh1: (f+g) n = (f n) + (g n) := by
        exact rfl
      rw [hh1]
      exact abs_add_le (f n) (g n)
    have hh2 : abs (f n) + abs (g n) < 1 / ↑n ^ c + abs (g n) := by
      exact (add_lt_add_iff_right (abs (g n))).mpr nfg_f
    have hh3 : abs (f n) + abs (g n) < 1 / ↑n ^ c + 1 / ↑n ^ c := by
      exact add_lt_add nfg_f nfg_g
    have hh4 : 1/(n:ℝ)^c + 1/(n:ℝ)^c = 2/(n:ℝ)^c  := by ring_nf
    rw [hh4] at hh3
    apply lt_of_le_of_lt this hh3
  apply Exists.intro nfg
  constructor
  · have : ng ≥ 0 := by
      exact Nat.zero_le ng
    have : nf+ng >0 := by apply Right.add_pos_of_pos_of_nonneg hf.1 this
    exact this
  · exact fun n a => le_of_lt (this n a)

lemma bounded_negl_negl {f g : ℕ → ℝ} (hg : negligible g): (∀ n, abs (f n) ≤ abs (g n)) → negligible f := by
  intro h c hc
  obtain ⟨n₀,hn₀⟩ := hg c hc
  use n₀
  rcases hn₀ with ⟨h1,h2⟩
  constructor
  · exact h1
  intro n hn
  exact lt_of_le_of_lt (h n) (h2 n hn)

lemma nat_mul_negl_negl {f : ℕ → ℝ} (m : ℕ) : negligible f → negligible (λ n => m * (f n)) := by
  intro hf
  induction m with
  | zero => norm_num; exact zero_negl
  | succ k ih =>
    norm_num
    have d : (λn => ((k : ℝ) + 1) * (f n)) = (λn => (k : ℝ) * (f n)) + (λn => f n) := by
      ring_nf
      rfl
    rw [d]
    exact negl_add_negl_negl ih hf

lemma const_mul_negl_negl  {f : ℕ → ℝ} (m : ℝ) : negligible f → negligible (λ n => m * (f n)) := by
  intro hf
  have arch := exists_nat_gt (abs m)
  obtain ⟨k,hk⟩ := arch
  apply bounded_negl_negl
  · exact nat_mul_negl_negl k hf
  · intro n
    have h : abs m ≤ abs (k : ℝ) := by
      refine Iff.mpr le_iff_lt_or_eq ?_
      left
      have : |(k : ℝ)| = (k : ℝ) := by
        exact abs_of_nonneg (Nat.cast_nonneg k)
      rw [this]
      assumption
    have (a b:ℝ): abs (a*b) = (abs a) * (abs b) := by
      exact abs_mul a b
    rw [this m (f n), this (k:ℝ) (f n)]
    refine mul_le_mul_of_nonneg_right h ?_
    exact abs_nonneg (f n)

lemma negligible_pow_two_inv : negligibleLO (fun n:ℕ => 1/(2^n)) := by
  unfold negligibleLO
  intro c c_pos
  apply isLittleO_of_inv_of_pos
  · exact isLittleO_rpow_of_exp c c_pos
  · norm_num
    use 1
    intro b hb
    refine pow_pos ?_ c
    exact Nat.cast_pos'.mpr hb
  · norm_num


/-
negligible (1/2^n) can be proven if x>0 → x^2 ≤ (log 2)*rexp x is proven.
Based on the graph of log2 rexp(x)-x^2, this is obviously true.
However, this analytic result is combersome to prove.
open Real

lemma pow_two_le_log2_mul_exp: ∀ x:ℝ, x>0 → x^2 ≤ (log 2)*rexp x := by sorry


theorem neg_exp_negl : negligible (λ n => (1 : ℝ) / 2 ^ n) := by
  rw [← negl_eq_neglLE]
  unfold negligibleLE
  intro c hc
  dsimp
  use Nat.ceil (Real.exp c)
  constructor
  · have : ∀ x:ℝ, rexp x > 0 := by exact fun x => exp_pos x
    exact Nat.ceil_pos.mpr (this ↑c)
  intro n hn
  have  : abs ((1:ℝ)/2^n) = (1:ℝ)/2^n := by
    have : (1:ℝ)/2^n > 0 := by
      refine one_div_pos.mpr ?_
      refine pow_pos ?_ n
      norm_num
    exact abs_of_pos this
  rw [this]
  have d_for_n: ∃ d:ℝ, c≤d ∧ ((rexp d) = n) := by
    have le_ceil: rexp (c:ℝ) ≤ Nat.ceil (rexp ↑c) := by exact Nat.le_ceil (rexp ↑c)
    use log n
    constructor
    · have : rexp ↑c ≤ n := by exact Nat.le_of_ceil_le hn
      have c_exp_log : ↑c=log (exp ↑c) := by exact Eq.symm (log_exp ↑c)
      rw [c_exp_log]
      refine log_le_log ?_ this
      exact exp_pos ↑c
    · refine exp_log ?_
      have one_le_rexp_c : rexp ↑c > 1 := by
        refine one_lt_exp_iff.mpr ?_
        exact Nat.cast_pos'.mpr hc
      have : (Nat.ceil (rexp ↑c):ℝ) ≤ (n:ℝ) := by exact Nat.cast_le.mpr hn
      linarith

  obtain ⟨d,hd1,hd2⟩ := d_for_n
  rw [← hd2]
  have : (2:ℝ)^n = (2:ℝ)^(n:ℝ) := by
    exact Eq.symm (rpow_natCast 2 n)
  rw [this,← hd2]
  refine one_div_le_one_div_of_le ?_ ?_
  · refine pow_pos ?_ c
    exact exp_pos d
  · refine le_rpow_of_log_le ?_ ?_
    · norm_num
    · rw [Real.log_pow]
      rw [log_exp]
      have hd3: ↑c * d ≤ d*d := by
        refine (mul_le_mul_iff_of_pos_right ?_).mpr hd1
        have : (c:ℝ)>0 := by exact Nat.cast_pos'.mpr hc
        linarith
      have hd4: d*d ≤ rexp d * log 2 := by
        have h1:= pow_two_le_log2_mul_exp d
        simp at h1
        rw [mul_comm,pow_two] at h1
        apply h1
        have : 0<(c:ℝ) := by exact Nat.cast_pos'.mpr hc
        linarith
      linarith
-/
