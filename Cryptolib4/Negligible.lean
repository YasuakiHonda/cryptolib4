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
        left
        rw [mul_comm]
      _ < 1 / (n : ℝ) ^ c := by
        refine (div_lt_div_iff_of_pos_right ?_).mpr ?_
        · exact pow_pos
        · exact k_div_n_le_one
  exact lt_of_le_of_lt H ineq

lemma neglK_imp_negl {f : ℕ→ℝ} : negligibleK f → negligible f := by
  unfold negligible negligibleK
  intro h
  intro c hc
  have hh := (h 1 (by linarith)) c hc
  assumption

lemma negl_imp_neglK {f : ℕ→ℝ} : negligible f → negligibleK f := by
  unfold negligible negligibleK
  intro h
  intro k k_pos c hc
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
    rw [one_div_lt]; assumption;
    have : 1/k > 0 := by exact one_div_pos.mpr k_pos
    linarith
    assumption
  -- 1 / n^(c+1) < k / n^c
  have knc_bound : 1 / (n : ℝ)^(c + 1) < k / (n : ℝ)^c := by
    calc
      1 / (n : ℝ)^(c + 1) = (1 / (n : ℝ)^c) * (1 / n : ℝ) := by
        rw [pow_succ, one_div_mul_one_div]
      _ < (1 / (n : ℝ)^c) * k := by
        refine (mul_lt_mul_left ?_).mpr hn_bound
        refine one_div_pos.mpr ?_
        have one_div_k_pos: 0<1/k := by
          exact one_div_pos.mpr k_pos
        have n_pos : (n : ℝ) > 0 := by linarith
        apply pow_pos
        linarith
      _ = k / (n : ℝ)^c := by rw [one_div_mul_eq_div]

  have h4 := h₃ n hn₀_le
  linarith

theorem neglK_eq_negl {f : ℕ→ℝ} : negligibleK f ↔ negligible f := by
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



def negligibleLO (f : ℕ → ℝ) :=
  ∀ c > 0, f =o[Filter.atTop] (λ n => 1 / (n : ℝ)^c)

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
