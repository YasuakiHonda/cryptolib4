/-
 -----------------------------------------------------------
  Correctness and semantic security of ElGamal public-key
  encryption scheme
 -----------------------------------------------------------
-/

import Cryptolib4.DDH
import Cryptolib4.PKE
import Cryptolib4.Tactics
import Cryptolib4.ToMathlib
import Cryptolib4.Uniform
import Init.Data.Nat.Div.Basic

noncomputable section ElGamal

variable (G : Type) [inst_1 : Fintype G] [inst_2 : CommGroup G] [inst_3 : DecidableEq G]
           (g : G) (g_gen_G : ∀ (x : G), x ∈ Subgroup.zpowers g)
           (q : ℕ) [inst_4 : Fact (0 < q)] [inst_5 : NeZero q]
           (G_card_q : Fintype.card G = q)
           (A_state : Type) (A1 : G → PMF (G × G × A_state))
           (A2 : G → G → A_state → PMF (ZMod 2))


def A2' : G × G → A_state → PMF (ZMod 2) := fun (gg : G × G) => A2 gg.1 gg.2

-- From Lupo: Generates a public key `g^x.val`, and private key `x`
def keygen : PMF (G × (ZMod q)) :=
  do
    let x ← uniform_zmod q
    pure (g^x.val, x)


-- From Lupo: encrypt takes a pair (public key, message)
def encrypt (pk m : G) : PMF (G × G) :=
  do
    let y ← uniform_zmod q
    pure (g^y.val, pk^y.val * m)

-- From Lupo: `x` is the secret key, `c.1` is g^y, the first part of the
-- cipher text returned from encrypt, and `c.2` is the
-- second value returned from encrypt
def decrypt (x : ZMod q) (c : G × G) : G := (c.2 / (c.1^x.val))

/-
  -----------------------------------------------------------
  Proof of correctness of ElGamal
  -----------------------------------------------------------
-/

omit inst_1 inst_3 inst_4 inst_5 in
lemma decrypt_eq_m (m : G) (x y : ZMod q) :
    decrypt G q x ((g^y.val), ((g^x.val)^y.val * m)) = m := by
  simp only [decrypt]
  rw [(pow_mul g x.val y.val).symm]
  rw [(pow_mul g y.val x.val).symm]
  rw [mul_comm y.val x.val]
  simp

omit inst_1 inst_4 in
theorem elgamal_correctness : pke_correctness (keygen G g q) (encrypt G g q) (decrypt G q) := by
  simp only [pke_correctness]
  intro m
  simp only [enc_dec, keygen, encrypt, bind]
  bind_skip_const
  simp [pure]
  bind_skip_const
  rw [decrypt_eq_m]
  simp

/-
  -----------------------------------------------------------
  Proof of semantic security of ElGamal
  -----------------------------------------------------------
-/

def D (gx gy gz : G) : PMF (ZMod 2) :=
  do
    let m ← A1 gx
    let b ← uniform_2
    let mb ← pure (if b = 0 then m.1 else m.2.1)
    let b' ← A2 gy (gz * mb) m.2.2
    pure (1 + b + b')

/- From Lupo:
  The probability of the attacker (i.e. the composition of A1 and A2)
  winning the semantic security game (i.e. guessing the correct bit),
  w.r.t. ElGamal is equal to the probability of D winning the game DDH0.
-/

omit inst_1 inst_3 inst_4 in
theorem SSG_DDH0 : SSG (keygen G g q) (encrypt G g q) A1 (A2' G A_state A2) =
  DDH0 G g q (D G A_state A1 A2) := by
    simp only [SSG, DDH0, bind, keygen, encrypt, D]
    simp_rw [PMF.bind_bind (uniform_zmod q)]
    bind_skip
    simp [pure]
    simp_rw [PMF.bind_comm (uniform_zmod q)]
    simp only [A2']
    repeat bind_skip
    rw [pow_mul g _ _]

def Game1 : PMF (ZMod 2) :=
  do
    let x ← uniform_zmod q
    let y ← uniform_zmod q
    let m ← A1 (g^x.val)
    let b ← uniform_2
    let ζ ← (do let z ← uniform_zmod q;
                let mb ← pure (if b = 0 then m.1 else m.2.1);
                pure (g^z.val * mb))
    let b' ← A2 (g^y.val) ζ m.2.2
    pure (1 + b + b')

def Game2 : PMF (ZMod 2) :=
  do
    let x ← uniform_zmod q
    let y ← uniform_zmod q
    let m ← A1 (g^x.val)
    let b ← uniform_2
    let ζ ← (do let z ← uniform_zmod q; pure (g^z.val))
    let b' ← A2 (g^y.val) ζ m.2.2
    pure (1 + b + b')

/- From Lupo:
  The probability of the attacker (i.e. the composition of A1 and A2)
  winning Game1 (i.e. guessing the correct bit) is equal to the
  probability of D winning the game DDH1.
-/
omit inst_1 inst_3 inst_4 in
theorem Game1_DDH1 : Game1 G g q A_state A1 A2 = DDH1 G g q (D G A_state A1 A2) := by
  simp only [DDH1, Game1, bind, D]
  repeat bind_skip
  simp_rw [PMF.bind_bind (A1 _)]
  rw [PMF.bind_comm (uniform_zmod q)]
  simp_rw [PMF.bind_bind (uniform_zmod q)]
  repeat bind_skip
  rw [PMF.bind_comm (uniform_2)]
  bind_skip
  rw [PMF.bind_bind (uniform_2)]
  simp_rw [PMF.bind_bind]
  repeat bind_skip
  simp [pure]


--ChatGPT tells me the skelton of the following proof
omit inst_3 inst_4 in
include g_gen_G G_card_q in
theorem ZMod_CyclicG_Surjective : ∀ x:G, ∃ n : ZMod q, g ^ n.val = x := by
  intro x
  -- 1) x = g^k for some k : ℤ
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp (g_gen_G x)
  -- 2) map k to Zmod and use it
  let n : ZMod q := k
  use n
  -- 3) g^q = 1
  have hq : g ^ q = 1 := by
    rw [← G_card_q]; exact pow_card_eq_one
  -- 4) show g^k is cyclic
  have h_pow_eq : g^k = g ^ (k % q) := by
    exact zpow_eq_zpow_emod' k hq
  have : n.val = (k % q) := by
    exact ZMod.val_intCast k
  rw [← this] at h_pow_eq
  rw [h_pow_eq]
  exact Eq.symm (zpow_natCast g n.val)

omit inst_3 inst_4 in
include inst_1 inst_2 g_gen_G G_card_q in
lemma exp_bij : Function.Bijective (fun (z : ZMod q) => g^z.val) := by
  apply (Fintype.bijective_iff_surjective_and_card _).mpr
  apply And.intro
  · -- surjective
    rw [Function.Surjective]
    exact fun b => ZMod_CyclicG_Surjective G g g_gen_G q G_card_q b
  · -- injective
    rw [G_card_q]
    exact ZMod.card q

omit inst_3 inst_4 in
include g_gen_G G_card_q in
lemma exp_mb_bij (mb : G) : Function.Bijective (fun (z : ZMod q) => g ^z.val * mb) := by
  have h : (fun (z : ZMod q)=> g ^ z.val * mb) =
    ((fun (m : G)=> (m * mb)) ∘ (fun (z : ZMod q)=> g ^ z.val)) := rfl
  rw [h]
  apply Function.Bijective.comp
  · --  (λ (m : G), (m * mb)) bijective
    apply (Fintype.bijective_iff_injective_and_card _).mpr
    apply And.intro
    · intro x a hxa
      simp at hxa
      exact hxa
    · rfl
  · -- (λ (z : zmod q), g ^ z.val) bijective
    exact exp_bij G g g_gen_G q G_card_q

omit inst_1 inst_2 inst_4 inst_5 in
lemma G1_G2_lemma1 (x : G) (exp : ZMod q → G) (y : ENNReal) (exp_bij : Function.Bijective exp) :
  (∑' (z : ZMod q), if (x = exp z) then (y : ENNReal) else 0) = y := by

    have inv := Function.bijective_iff_has_inverse.mp exp_bij
    cases inv with
    | intro exp_inv inv_h =>
      have bij_eq : ∀ (z : ZMod q), (x = exp z) = (z = exp_inv x) := by
        intro z
        ext
        apply Iff.intro
        · -- Left to right
          intro h
          rw [← inv_h.left z]
          exact (congr_arg exp_inv h).symm
        · -- Right to left
          intro h
          rw [← inv_h.right x]
          exact (congr_arg exp h).symm
      simp_rw [bij_eq]
      simp

omit inst_4 in
include g_gen_G G_card_q in
lemma G1_G2_lemma2 (mb : G) :
  (uniform_zmod q).bind (fun (z : ZMod q)=> pure (g^z.val * mb)) =
  (uniform_zmod q).bind (fun (z : ZMod q)=> pure (g^z.val)) := by
    simp [PMF.bind]
    simp_rw [uniform_zmod_prob]
    ext x
    simp [pure, PMF.pure, DFunLike.coe]
    have rval : (∑' (a : ZMod q), if x = g ^ a.val then (q:ENNReal)⁻¹ else 0) = (↑q)⁻¹ := by
      apply G1_G2_lemma1
      apply exp_bij
      · exact fun x => g_gen_G x
      · exact G_card_q

    have lval : (∑' (a : ZMod q), if x = g ^ a.val * mb then (q:ENNReal)⁻¹ else 0) = (↑q)⁻¹ := by
      apply G1_G2_lemma1
      apply exp_mb_bij
      · exact fun x => g_gen_G x
      · exact G_card_q
    rw [rval,lval]

omit inst_4 in
include g_gen_G G_card_q in
lemma G1_G2_lemma3 (m : PMF G) :
  m.bind (fun (mb : G)=> (uniform_zmod q).bind (fun (z : ZMod q)=> pure (g^z.val * mb))) =
  (uniform_zmod q).bind (fun (z : ZMod q)=> pure (g^z.val)) := by
    simp_rw [G1_G2_lemma2 G g g_gen_G q G_card_q _]
    bind_skip_const
    congr

/- From Lupo:
  The probability of the attacker (i.e. the composition of A1 and A2)
  winning Game1 (i.e. guessing the correct bit) is equal to the
  probability of the attacker winning Game2.
-/
omit inst_4 in
include g_gen_G G_card_q in
theorem Game1_Game2 : Game1 G g q A_state A1 A2 = Game2 G g q A_state A1 A2 := by
  simp only [Game1, Game2]
  bind_skip
  bind_skip
  bind_skip
  bind_skip
  simp [bind, -PMF.bind_pure, -PMF.bind_bind]
  simp_rw [PMF.bind_comm (uniform_zmod q)]
  rw [G1_G2_lemma3 G g g_gen_G q G_card_q _ ]


lemma G2_uniform_lemma (b' : ZMod 2) :
  uniform_2.bind (fun (b : ZMod 2)=> pure (1 + b + b')) = uniform_2 := by
    fin_cases b'
    · ring_nf
      ext; rename ZMod 2 => a
      simp [uniform_2]
      simp_rw [uniform_zmod_prob]
      simp [ENNReal.tsum_mul_left]
      have zmod_eq_comm : ∀(x : ZMod 2), (a = 1+ x) = (x = 1 + a) := by
        intro x
        fin_cases a <;> fin_cases x <;> simp <;> exact rfl
      have h : (∑' (x : ZMod 2), (pure (1 + x) : PMF (ZMod 2)) a) = 1 := by
        simp [pure, PMF.pure, DFunLike.coe]
        simp_rw [zmod_eq_comm]
        simp
      rw [h]
      simp
    · ring_nf
      ext
      simp [uniform_2, DFunLike.coe]
      have h : uniform_2.bind (fun (b : ZMod 2) => pure (0 + b)) = uniform_2 := by simp [pure]
      ring_nf
      have h_zmod : (2 : ZMod 2) = 0 := rfl
      rw [h_zmod]
      exact congrFun (congrArg Subtype.val h) _

/- From Lupo:
  The probability of the attacker (i.e. the composition of A1 and A2)
  winning Game2 (i.e. guessing the correct bit) is equal to a coin flip.
-/
omit inst_1 inst_3 inst_4 in
theorem Game2_uniform : Game2 G g q A_state A1 A2  = uniform_2 := by
  simp [Game2, bind]
  bind_skip_const
  bind_skip_const
  bind_skip_const
  simp_rw [PMF.bind_comm uniform_2]
  bind_skip_const
  bind_skip_const
  bind_skip_const
  exact G2_uniform_lemma _

variable (ε : ENNReal)

/- From Lupo:
  The advantage of the attacker (i.e. the composition of A1 and A2) in
  the semantic security game `ε` is exactly equal to the advantage of D in
  the Diffie-Hellman game. Therefore, assumining the decisional Diffie-Hellman
  assumption holds for the group `G`, we conclude `ε` is negligble, and
  therefore ElGamal is, by definition, semantically secure.
-/
omit inst_4 in
include g_gen_G G_card_q in
theorem elgamal_semantic_security (DDH_G : DDH G g q (D G A_state A1 A2) ε) :
  pke_semantic_security (keygen G g q) (encrypt G g q) A1 (A2' G A_state A2) ε := by
    simp only [pke_semantic_security]
    rw [SSG_DDH0]
    have h : uniform_2 1 = 1/2 := by
      simp only [uniform_2]
      rw [uniform_zmod_prob 1]
      norm_cast
    rw [← h]
    rw [← Game2_uniform G g q A_state A1 A2]
    rw [← Game1_Game2 G g g_gen_G q G_card_q A_state A1 A2]
    rw [Game1_DDH1]
    exact DDH_G

end ElGamal
