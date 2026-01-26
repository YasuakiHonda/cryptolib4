import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Order.Filter.Defs
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
  intro negf c hc
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


/-
Two versions of negligible functions: a constant k is put on the denominator.
The first one looks stronger because it talks on any k > 0.
The second one looks weaker because it talks on some k > 0.
However, they are equivalent.
Also, they are equivalent to the original definition of the negligible function.
-/
def negligibleK (f : ℕ → ℝ) :=
  ∀ k>0, ∀ c > 0, ∃ n₀>0, ∀ n, n₀ ≤ n → abs (f n) < k / (n : ℝ)^c

def negligibleK_ex (f : ℕ → ℝ) :=
  ∃ k>0, ∀ c > 0, ∃ n₀>0, ∀ n, n₀ ≤ n → abs (f n) ≤ k / (n : ℝ)^c

lemma neglK_imp_neglK_ex (f : ℕ → ℝ) : negligibleK f → negligibleK_ex f := by
  unfold negligibleK negligibleK_ex
  intro h
  use 1
  constructor
  · norm_num
  intro c hc
  obtain ⟨n₀, n₀_pos, h2⟩ := h 1 (by linarith) c hc
  use n₀
  constructor
  · assumption
  intro n hn
  exact le_of_lt (h2 n hn)

lemma neglK_ex_imp_negl {f : ℕ → ℝ} :
    negligibleK_ex f → negligible f := by
  rintro ⟨k, k_pos, hk⟩
  intro c c_pos

  -- 目標: ∃ n₀, ∀ n ≥ n₀, |f n| < 1 / n^c
  -- まず c' を調整する：k / n^{c'} < 1 / n^c ⇔ k < n^{c' - c}
  -- c' = c + δ にすれば OK

  let δ := 1
  let c' := c + δ
  have c'_pos : c' > 0 := by exact Nat.add_pos_left c_pos δ

  obtain ⟨n₀, hn₀_pos, H⟩ := hk c' c'_pos
  use max n₀ (Nat.ceil (k+1))
  constructor
  · exact lt_sup_of_lt_left hn₀_pos
  intro n hn
  have : ⌈k+1⌉₊ ≤ n := by exact le_of_max_le_right hn
  have : k+1 ≤ (n:ℝ) := by exact Nat.le_of_ceil_le this
  have k_lt_n : k < (n:ℝ) := by
    have : k < k+1 := by exact lt_add_one k
    linarith
  have k_div_n_le_one : k / (n : ℝ) < 1 := by
    refine (div_lt_one ?_).mpr k_lt_n
    linarith
  have n₀_le_n : n₀ ≤ n := by exact le_of_max_le_left hn

  specialize H n n₀_le_n
  -- |f n| ≤ k / n^{c + 1}
  -- これが 1 / n^c より小さいことを示す
  have n_pos : n > 0 := by linarith
  have pos_n : (n : ℝ) > 0 := Nat.cast_pos.mpr n_pos

  have pow_pos : (n : ℝ)^c > 0 := by
    exact pow_pos pos_n c
  have ineq : k / (n : ℝ) ^ c' < 1 / (n : ℝ) ^ c := by
    calc
      k / (n : ℝ) ^ c' = (k / (n : ℝ)) / (n : ℝ) ^ c := by
        rw [pow_succ]
        field_simp
      _ < 1 / (n : ℝ) ^ c := by
        refine (div_lt_div_iff_of_pos_right ?_).mpr ?_
        · exact pow_pos
        · exact k_div_n_le_one
  exact lt_of_le_of_lt H ineq

lemma neglK_imp_negl {f : ℕ → ℝ} : negligibleK f → negligible f := by
  unfold negligible negligibleK
  intro h c hc
  have hh := (h 1 (by linarith)) c hc
  assumption

lemma negl_imp_neglK {f : ℕ → ℝ} : negligible f → negligibleK f := by
  unfold negligible negligibleK
  intro h k k_pos c hc
  have hk := h c hc

  -- use c+1 with negligibleK
  have hc1 : c + 1 > 0 := by linarith
  have h₂ := h (c + 1) hc1
  obtain ⟨n₀, hn₀, h₃⟩ := h₂

  -- define n₁ = max(n₀, ⌈k⌉ + 1)
  let n₁ := max n₀ ((Nat.ceil (1/k)) + 1)
  use n₁

  constructor
  · have : n₁ ≥ n₀ := by exact Nat.le_max_left n₀ (Nat.ceil (1/k) + 1)
    exact Nat.lt_of_lt_of_le hn₀ this

  intro n hn
  have hn₀_le : n₀ ≤ n := le_trans (le_max_left _ _) hn
  have hk_bound : 1/k < n := by
    have t1: Nat.ceil (1/k) + 1 ≤ n := by exact le_of_max_le_right hn
    exact Nat.lt_of_ceil_lt t1
  have hn_bound : 1/(n:ℝ) < k := by
    rw [one_div_lt];
    · assumption
    · have : 1/k > 0 := by exact one_div_pos.mpr k_pos
      linarith
    · linarith

  -- 1 / n^(c+1) < k / n^c
  have knc_bound : 1 / (n : ℝ)^(c + 1) < k / (n : ℝ)^c := by
    calc
      1 / (n : ℝ)^(c + 1) = (1 / (n : ℝ)^c) * (1 / n : ℝ) := by
        rw [pow_succ, one_div_mul_one_div]
      _ < (1 / (n : ℝ)^c) * k := by
        refine (mul_lt_mul_iff_right₀ ?_).mpr hn_bound
        refine one_div_pos.mpr ?_
        have one_div_k_pos: 0<1/k := by
          exact one_div_pos.mpr k_pos
        have n_pos : (n : ℝ) > 0 := by linarith
        apply pow_pos
        linarith
      _ = k / (n : ℝ)^c := by rw [one_div_mul_eq_div]

  have h4 := h₃ n hn₀_le
  linarith

theorem neglK_eq_negl {f : ℕ → ℝ} : negligibleK f ↔ negligible f := by
  constructor
  · exact fun a => neglK_imp_negl a
  · exact fun a => negl_imp_neglK a

lemma neglK_ex_imp_neglK {f : ℕ → ℝ} : negligibleK_ex f → negligibleK f := by
  intro h
  rw [neglK_eq_negl]
  exact neglK_ex_imp_negl h

theorem neglK_eq_neglK_ex {f : ℕ → ℝ} : negligibleK f ↔ negligibleK_ex f := by
  constructor
  · exact fun a => neglK_imp_neglK_ex f a
  · exact fun a => neglK_ex_imp_neglK a


def negligibleLO (f : ℕ → ℝ) :=
  ∀ c > 0, f =o[Filter.atTop] (fun n => 1 / (n : ℝ)^c)

lemma neglLO_imp_neglLE (f : ℕ → ℝ) : negligibleLO f → negligibleLE f := by
  unfold negligibleLO negligibleLE
  intro h c c_pos
  have h1 := h c c_pos
  rw [Asymptotics.isLittleO_iff] at h1
  norm_num at h1
  have h3 := @h1 1 (by linarith)

  obtain ⟨n₁, h4⟩ := h3
  field_simp at h4
  use max n₁ 1
  constructor
  · have : max n₁ 1 ≥ 1 := by exact Nat.le_max_right n₁ 1
    linarith
  intro n hn
  have : n₁≤n := by exact le_of_max_le_left hn
  have h5 := h4 n this
  assumption

lemma neglK_imp_neglLO (f : ℕ → ℝ) : negligibleK f → negligibleLO f := by
  unfold negligibleLO negligibleK
  intro h1 c c_pos
  rw [Asymptotics.isLittleO_iff]
  norm_num
  intro d d_pos

  have h2 := h1 d d_pos c c_pos
  obtain ⟨n₀, n₀_pos, h3⟩ := h2
  use n₀
  intro n' n'_pos
  have h4 := h3 n' n'_pos
  exact le_of_lt (h3 n' n'_pos)

theorem neglLO_eq_negl (f : ℕ → ℝ) : negligibleLO f ↔ negligible f := by
  constructor
  · intro h
    refine (negl_eq_neglLE f).mp ?_
    exact neglLO_imp_neglLE f h
  · intro h
    refine neglK_imp_neglLO f ?_
    exact negl_imp_neglK h


open Filter Asymptotics

/-- Main theorem: If `f = o(g)` and both positive eventually,
    then `1/g = o(1/f)` -/
theorem isLittleO_of_inv_of_pos {f g : ℕ → ℝ} (h : f =o[atTop] g)
    (hf : ∀ᶠ x in atTop, 0 < f x)
    (hg : ∀ᶠ x in atTop, 0 < g x) :
    (fun x => 1 / g x) =o[atTop] (fun x => 1 / f x) := by
  rw [isLittleO_iff] at h ⊢
  intro k k_pos

  -- Combine all eventual conditions
  have := hf.and (hg.and (h k_pos))
  obtain ⟨N, hN⟩ := eventually_atTop.mp this
  norm_num

  use N
  intro n hn
  specialize hN n hn
  rcases hN with ⟨hf, hg, hfg⟩
  have hfg_pos : 0 < |f n| := by
    exact abs_pos_of_pos hf
  have hfg_pos2 : 0 < |g n| := by
    exact abs_pos_of_pos hg
  norm_num  at hfg
  field_simp

  rw [mul_comm]
  exact hfg

lemma isLittleO_rpow_of_exp :
  ∀ c>0, (fun x:ℕ => (x:ℝ)^c) =o[atTop] (fun x:ℕ => (2:ℝ) ^ x) := by
  intro c c_pos
  have h1 := @isLittleO_pow_exp_pos_mul_atTop c (Real.log 2) (by refine Real.log_pos ?_; norm_num)
  have h2: (fun x:ℝ=>(2:ℝ)^x) = (fun x:ℝ => Real.exp (Real.log 2 * x)) := by
    funext x
    apply Real.rpow_def_of_pos
    linarith
  rw [← h2] at h1
  refine isLittleO_pow_const_const_pow_of_one_lt c ?_
  linarith
