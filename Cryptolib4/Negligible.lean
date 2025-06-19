import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Order.Filter.Defs
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic


/- From Lupo:
  A function f : ℤ≥1 → ℝ is called negligible if
  for all c ∈ ℝ>0 there exists n₀ ∈ ℤ≥1 such that
  n₀ ≤ n →  |f(n)| < 1/n^c
-/


def negligible (f : ℕ → ℝ) :=
  ∀ c > 0, ∃ n₀>0, ∀ n, n₀ ≤ n → abs (f n) < 1 / (n : ℝ)^c

def negligibleLE (f : ℕ → ℝ) :=
  ∀ c > 0, ∃ n₀>0, ∀ n, n₀ ≤ n → abs (f n) ≤ 1 / (n : ℝ)^c

lemma negl_imp_neglLE (f : ℕ → ℝ) : negligible f → negligibleLE f := by
  unfold negligible negligibleLE
  intro negf
  intro c hc
  obtain ⟨n₀,hn₀_pos,h1⟩ := negf c hc
  use n₀
  constructor
  · assumption
  intro n hn
  have h2 := h1 n hn
  exact le_of_lt (h1 n hn)


lemma neglLE_imp_negl (f : ℕ → ℝ) : negligibleLE f → negligible f := by
  intro h c hc
  have hh := (h (c + 1) (Nat.succ_pos c))
  obtain ⟨N,hNpos,hN⟩ := hh

  use N+1
  constructor
  · linarith
  intro n hn
  -- 1 / n^(c + 1) = (1 / n^c) * (1 / n)
  have n_ge_N : n ≥ N := by linarith
  have hh1 := hN n n_ge_N
  have : 1 / (n : ℝ)^(c + 1) = (1 / (n : ℝ)^c) * (1 / n:ℝ) := by
    rw [pow_succ, one_div_mul_one_div]
  rw [this] at hh1
  have n_ge_2 : 2 ≤ n := by
    have hN : 1 ≤ N := Nat.succ_le_of_lt hNpos
    have h2_le_Np1 : 2 ≤ N + 1 := Nat.add_le_add_right hN 1
    exact le_trans h2_le_Np1 hn

  have mult_lt : (1 / (n : ℝ)^c) * (1 / n:ℝ) < 1 / (n : ℝ)^c := by
    have hnR : (2 : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr n_ge_2
    have h_inv_lt_one : 1 / (n : ℝ) < 1 := by
      refine Bound.div_lt_one_of_pos_of_lt ?_ ?_
      · linarith
      · linarith
    have hpow_pos : 0 < (n : ℝ)^c := by
      apply pow_pos
      linarith
    refine mul_lt_of_lt_one_right ?_ h_inv_lt_one
    exact one_div_pos.mpr hpow_pos
  exact lt_of_le_of_lt hh1 mult_lt

theorem negl_eq_neglLE (f : ℕ → ℝ) : negligibleLE f ↔ negligible f := by
  constructor
  · exact fun a => neglLE_imp_negl f a
  · exact fun a => negl_imp_neglLE f a

def negligibleK (f : ℕ → ℝ) :=
  ∃ k:NNReal, ∀ c > 0, ∃ n₀>0, ∀ n, n₀ ≤ n → abs (f n) < k / (n : ℝ)^c

lemma neglK_negl {f : ℕ→ℝ} : negligibleK f → negligible f := by
  intro h
  obtain ⟨k, hk⟩ := h
  intro c hc

  by_cases k_pos : k > 0
  case pos =>
    -- use c+1 with negligibleK
    have hc1 : c + 1 > 0 := by linarith
    obtain ⟨n₀, hn₀, h₁⟩ := hk (c+1) hc1

    -- define n₁ = max(n₀, ⌈k⌉ + 1)
    let n₁ := max n₀ (Nat.ceil k + 1)
    use max n₀ (Nat.ceil k + 1)

    constructor
    · have : n₀ ⊔ (⌈k⌉₊ + 1) ≥ n₀ := by exact Nat.le_max_left n₀ (⌈k⌉₊ + 1)
      exact Nat.lt_of_lt_of_le hn₀ this

    intro n hn
    have hn₀_le : n₀ ≤ n := le_trans (le_max_left _ _) hn
    have hk_bound : k < n := by
      have : Nat.ceil k + 1 ≤ n := le_trans (le_max_right _ _) hn
      have : k ≤ Nat.ceil k := Nat.le_ceil k
      (expose_names; exact Nat.lt_of_ceil_lt this_1)

    have h1 : abs (f n) < k / (n : ℝ)^(c + 1) := by
      apply h₁; assumption

    -- k / n^(c+1) < 1 / n^c
    have h2 : k / (n : NNReal)^(c + 1) < 1 / (n : NNReal)^c := by
      have n_pos : (n : NNReal) > 0 := by exact gt_trans hk_bound k_pos
      rw [div_lt_div_iff₀]
      · ring_nf
        field_simp
        exact hk_bound
      · exact pow_pos n_pos (c + 1)
      · exact pow_pos n_pos c

    exact lt_trans h1 h2

  case neg =>
    obtain ⟨n₀, hn₀, hh⟩ := hk c hc
    use n₀
    constructor
    · exact hn₀
    intro n hn

    have h1 : abs (f n) < k / (n : NNReal)^c := by
      apply hh; assumption
    have h2 : k / (n : NNReal)^c ≤ 0 := by
      apply div_nonpos_of_nonpos_of_nonneg (le_of_not_gt k_pos)
      exact pow_nonneg (Nat.cast_nonneg n) c
    have h3 : 0 < 1/(n : NNReal)^c := by
      have : 0 < n := by exact Nat.lt_of_lt_of_le hn₀ hn
      have : 0 < (n:NNReal) := by exact Nat.cast_pos'.mpr this
      have : 0 < (n:NNReal)^c := by exact pow_pos this c
      exact one_div_pos.mpr this
    have h4 : abs (f n) < 0 := by
      apply lt_of_lt_of_le h1 h2
    apply lt_trans h4 h3

theorem neglK_eq_negl {f : ℕ→ℝ} : negligibleK f ↔ negligible f := by
  constructor
  · exact fun a => neglK_negl a
  · intro hf
    rw [negligibleK]
    use 1
    exact fun c a => hf c a

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
  rw [negligibleK]
  use 2
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
  · assumption

lemma bounded_negl_negl {f g : ℕ → ℝ} (hg : negligible g): (∀ n, abs (f n) ≤ abs (g n)) → negligible f := by
  intro h c hc
  obtain ⟨n₀,hn₀⟩ := hg c hc
  use n₀
  rcases hn₀ with ⟨h1,h2⟩
  constructor
  · exact h1
  intro n hn
  exact gt_of_gt_of_ge (h2 n hn) (h n)

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

open Real

lemma pow_two_le_log2_mul_exp: (fun x => x^2) ≤ (fun x=> (log 2)*rexp x) := by sorry


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
        assumption

      /-
        f(x):=(log 2)*rexp x - x^2
        graph clearly shows that f(x)>0 for x≥0.
        The formal proof should be a bit complex than thought.
        For instance, f(0)=log 2 but f(x) is not monotone.
        f'(x)=(log 2)*rexp x - 2*x has two zeros, log 2 and 2*log 2.
        f'(log 2)=(log 2)*2 - 2* log 2=0
        f'(2*log 2)=(log 2)*2*2 - 2* 2*log 2=0
        f''(x) = (log 2)*rexp x - 2
        f''(log 2)=2*(log 2) - 2=2*((log 2) - 1) < 0
        f''(2*log 2)= 4*(log 2) - 2 = 2*(2*(log 2) -1) > 0
      -/
      linarith
