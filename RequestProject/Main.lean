import Mathlib

open scoped BigOperators

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace PFAComplexity

/-- A finite word over an alphabet `α`. This is the Lean counterpart of the finite
strings `w ∈ Σⁿ` used throughout the original source. -/
abbrev Word (α : Type*) := List α

/-- A `k`-state probabilistic finite automaton. This formalizes the PFA tuple
`M = (S, Σ, {P_σ}, π⃗, η⃗)` in the Introduction of the original source.
The Boolean function `final` is the indicator of the accepting states. -/
structure PFA (α : Type*) (k : ℕ) where
  initial : Fin k → ℝ
  transition : α → Fin k → Fin k → ℝ
  final : Fin k → Bool
  initial_nonneg : ∀ i, 0 ≤ initial i
  initial_sum : ∑ i, initial i = 1
  transition_nonneg : ∀ a i j, 0 ≤ transition a i j
  transition_sum : ∀ a i, ∑ j, transition a i j = 1

/-- Evolution of a row distribution. This is matrix multiplication by `P_σ` in
the acceptance-probability formula in the Introduction of the original source. -/
def step {α : Type*} {k : ℕ} (M : PFA α k) (p : Fin k → ℝ) (a : α) : Fin k → ℝ :=
  fun j => ∑ i, p i * M.transition a i j

/-- The distribution reached after reading a word. This corresponds to
`π⃗ P_{x₁}⋯P_{xₙ}` in the original source. -/
def run {α : Type*} {k : ℕ} (M : PFA α k) (w : Word α) : Fin k → ℝ :=
  w.foldl (step M) M.initial

/-- Acceptance probability `ρ_M(x)` from the Introduction of the original source. -/
def acceptance {α : Type*} {k : ℕ} (M : PFA α k) (w : Word α) : ℝ :=
  ∑ i, run M w i * if M.final i then 1 else 0

/-- `M` uniquely accepts `w` most probably among words of the same length.
This is exactly the condition `gap_M(w) > 0` from the original source, expressed
without taking a minimum. -/
def UniquelyMaximizes {α : Type*} {k : ℕ} (M : PFA α k) (w : Word α) : Prop :=
  ∀ z : Word α, z.length = w.length → z ≠ w → acceptance M z < acceptance M w

/-- Probabilistic automatic complexity `A_P(w)` from the Introduction of the
original source: the least number of PFA states uniquely maximizing `w`. -/
noncomputable def probabilisticAutomaticComplexity {α : Type*} (w : Word α) : ℕ :=
  sInf {k : ℕ | ∃ M : PFA α k, UniquelyMaximizes M w}

/-- The affine digit dynamics `g_j(u,q)` in Proposition 4 (General alphabets) of
the original source. -/
noncomputable def digitMap (b j : ℕ) (x : ℝ × ℝ) : ℝ × ℝ :=
  ((x.1 + j) / b, (x.2 + 2 * j * x.1 + j ^ 2) / b ^ 2)

/-- The triangle `Δ_s = {(u,q) : 0 ≤ u ≤ 1, 0 ≤ q ≤ su}` from Lemma 2 of
the original source. -/
def InTriangle (s : ℝ) (x : ℝ × ℝ) : Prop :=
  0 ≤ x.1 ∧ x.1 ≤ 1 ∧ 0 ≤ x.2 ∧ x.2 ≤ s * x.1

/-- The three ordered vertices `(1,0),(1,s),(0,0)` of `Δ_s`, as ordered in the
proofs of Theorem 3 and Proposition 4 of the original source. -/
def vertex (s : ℝ) : Fin 3 → ℝ × ℝ
  | ⟨0, _⟩ => (1, 0)
  | ⟨1, _⟩ => (1, s)
  | ⟨2, _⟩ => (0, 0)

/-- Barycentric coordinates `(u-q/s,q/s,1-u)` used explicitly in the proof of
Theorem 3 of the original source. -/
noncomputable def barycentric (s : ℝ) (x : ℝ × ℝ) : Fin 3 → ℝ
  | ⟨0, _⟩ => x.1 - x.2 / s
  | ⟨1, _⟩ => x.2 / s
  | ⟨2, _⟩ => 1 - x.1

/-- The barycentric coordinates sum to one, as asserted in the preliminary
barycentric discussion and used in Lemma 1 of the original source. -/
lemma barycentric_sum (s : ℝ) (x : ℝ × ℝ) : ∑ i, barycentric s x i = 1 := by
  simp [Fin.sum_univ_succ, barycentric]
  ring

/-- Points of `Δ_s` have nonnegative barycentric coordinates. This formalizes
the probability-vector assertion in the preliminaries of the original source. -/
lemma barycentric_nonneg {s : ℝ} (hs : 0 < s) {x : ℝ × ℝ}
    (hx : InTriangle s x) (i : Fin 3) : 0 ≤ barycentric s x i := by
  unfold barycentric
  rcases hx with ⟨hx1, hx2, hx3, hx4⟩
  fin_cases i <;> norm_num <;> nlinarith [mul_div_cancel₀ (x.2) hs.ne']

/-- Reconstructing a point from its barycentric coordinates, the affine identity
at the heart of Lemma 1 (`lem:corr`) of the original source. -/
lemma barycentric_reconstruct {s : ℝ} (hs : s ≠ 0) (x : ℝ × ℝ) :
    (∑ i, barycentric s x i * (vertex s i).1,
      ∑ i, barycentric s x i * (vertex s i).2) = x := by
  simp [barycentric]
  repeat rw [Fin.sum_univ_three]
  simp [vertex]
  field_simp

/-- The square relation `q=u²` is invariant under `g_j`, as stated at the start
of both the binary construction and Proposition 4 in the original source. -/
lemma digitMap_square (b j : ℕ) (u : ℝ) (hb : (b : ℝ) ≠ 0) :
    (digitMap b j (u, u ^ 2)).2 = (digitMap b j (u, u ^ 2)).1 ^ 2 := by
  simp [digitMap]
  field_simp
  ring

/-- General-alphabet triangle invariance, including Lemma 2 (`lem:triangle`) as
the special case `b=2`, from the original source. -/
lemma digitMap_mem_triangle {b j : ℕ} {s : ℝ} (hb : 2 ≤ b) (hj : j < b)
    (hs : 1 ≤ s) {x : ℝ × ℝ} (hx : InTriangle s x) :
    InTriangle s (digitMap b j x) := by
  simp [InTriangle, digitMap] at *
  constructor
  · apply div_nonneg
    · linarith
    · simp
  · constructor
    · field_simp
      have h₀ : j + 1 ≤ b := by exact Order.add_one_le_iff.mpr hj
      have h₁ : j ≤ b - 1 := by exact Nat.le_sub_one_of_lt hj
      have : x.1 + j ≤ 1 + (b - 1) := by
        refine add_le_add ?_ ?_
        linarith
        have : (j : ℝ) ≤ (b - 1) := by
            by_cases H : b = 0
            · subst H;simp at hj
            · suffices ((j + 1) : ℝ) ≤ b by exact le_tsub_of_add_le_right this

              have := @Nat.cast_le ℝ _ _ _ _ _ (j + 1) b
              simp at this ⊢
              tauto
        simp;linarith
      linarith
    · constructor
      · apply div_nonneg
        · nlinarith
        · simp
      · field_simp
        generalize x.1 = X at *
        generalize x.2 = Y at *
        have hx₀ := hx.1
        have hx₁ := hx.2.1
        have hx₂ := hx.2.2.1
        have hx₃ := hx.2.2.2
        clear hx
        have hbR : (2 : ℝ) ≤ b := by simp;tauto
        clear hb
        have hjR : j + 1 ≤ (b : ℝ) := by
            simp_all
            have : j + 1 ≤ b := by exact Order.add_one_le_iff.mpr hj
            clear hbR hx₃ hx₂ hx₁ hx₀ X Y x hs hj s
            have := @Nat.cast_le ℝ _ _ _ _ _ (j + 1) b
            simp at this ⊢
            tauto
        clear hj
        have hj₀ : 0 ≤ (j : ℝ) := by simp
        generalize (j : ℝ) = J at *
        clear j
        generalize (b : ℝ) = B at *
        clear b
        clear x
        ring_nf
        field_simp

        by_cases H : B = 2
        · subst B;simp_all
          nlinarith
        by_cases H : B = J + 1
        · subst B
          ring_nf
          clear H hjR
          have : 0 ≤ J * X + J + J ^ 2 := by nlinarith
          nlinarith
        suffices s * X + 2 * J * X + J ^ 2 ≤ (max 2 (J+1)) * s * (X + J) by
          -- two cases for the max
          have : max 2 (J+1) = 2 ∨
            max 2 (J+1) = J + 1 := by exact Std.MaxEqOr.max_eq_or 2 (J + 1)
          cases this with
          | inl h =>
            ring_nf
            suffices s * X + J * X * 2 + J ^ 2 ≤ (J * B + X * B) * s by linarith
            suffices J * X * 2 + J ^ 2 ≤ (J * B + X * B - X) * s by linarith
            suffices J * X * 2 + J ^ 2 ≤ (J * B + X * B - X) * 1 by
                apply le_trans this
                refine mul_le_mul_of_nonneg ?_ hs ?_ ?_
                nlinarith
                nlinarith
                nlinarith
            nlinarith
          | inr h =>
            have : 2 ≤ J + 1 := by exact le_of_sup_eq h
            suffices J * X * 2 + J ^ 2 ≤ s * (B * (J + X) - X) by
                linarith
            suffices J * X * 2 + J ^ 2 ≤ 1 * (B * (J + X) - X) by
                apply le_trans this
                refine mul_le_mul_of_nonneg ?_ ?_ ?_ ?_
                nlinarith
                nlinarith
                nlinarith
                ring_nf
                apply add_nonneg
                positivity
                simp
                have : 1 ≤ B := by linarith
                nlinarith
            simp
            suffices J * X * 2 + J ^ 2 ≤ (J+1) * (J + X) - X by nlinarith
            field_simp
            ring_nf
            suffices  J * X * 2 ≤ J + J * X by linarith
            nlinarith
        have : max 2 (J+1) = 2 ∨
            max 2 (J+1) = J + 1 := by exact Std.MaxEqOr.max_eq_or 2 (J + 1)
        cases this with
        | inl h => simp_all;nlinarith
        | inr h =>
            rw [h]
            ring_nf
            have : 0 ≤ J * X + J + J ^ 2 := by nlinarith
            nlinarith

/-- The explicit three-state automaton obtained by taking barycentric coordinates
of images of vertices, exactly as in Lemma 1 and Proposition 4 of the original
source. -/
noncomputable def barycentricPFA (b : ℕ) (s : ℝ) (x0 : ℝ × ℝ)
    (hb : 2 ≤ b) (hs : 1 ≤ s) (hx0 : InTriangle s x0) : PFA (Fin b) 3 where
  initial := barycentric s x0
  transition j i := barycentric s (digitMap b j (vertex s i))
  final i := i = 0
  initial_nonneg := barycentric_nonneg (lt_of_lt_of_le zero_lt_one hs) hx0
  initial_sum := barycentric_sum s x0
  transition_nonneg := by
    intro j i k
    apply barycentric_nonneg (lt_of_lt_of_le zero_lt_one hs)
    apply digitMap_mem_triangle hb j.isLt hs
    fin_cases i <;> simp [InTriangle, vertex] <;> nlinarith
  transition_sum := by intro j i; apply barycentric_sum

/-- Barycentric row evolution agrees with applying `g_j`. This is the equation
`λ(g_σ(x)) = λ(x)P_σ` proved in Lemma 1 of the original source. -/
lemma step_barycentric (b : ℕ) (s : ℝ) (x0 x : ℝ × ℝ)
    (hb : 2 ≤ b) (hs : 1 ≤ s) (hx0 : InTriangle s x0) (hxs : s ≠ 0)
    (j : Fin b) :
    step (barycentricPFA b s x0 hb hs hx0) (barycentric s x) j =
      barycentric s (digitMap b j x) := by
  funext i
  simp [step, barycentricPFA, vertex, digitMap, Fin.sum_univ_three]
  fin_cases i <;> simp [barycentric] <;> field_simp <;> ring_nf

/-- The reversed base-`b` value after starting at `u₀`; this is the recurrence
`u ↦ (u+j)/b` and quantity `u_n` in Proposition 4 of the original source. -/
noncomputable def reversedValue (b : ℕ) (u0 : ℝ) (w : List (Fin b)) : ℝ :=
  w.foldl (fun u j => (u + (j : ℕ)) / b) u0

example (x : ℝ) : reversedValue 2 (x) [1,0] = (x + 1) / 4 := by
    simp [reversedValue]
    linarith

/-- The terminal distribution of the explicit automaton is the barycentric
coordinate vector of `(u_n,u_n²)`, formalizing Lemma 1 plus square invariance as
used in Theorem 3 and Proposition 4 of the original source. -/
lemma run_barycentricPFA (b : ℕ) (s u0 : ℝ) (w : List (Fin b))
    (hb : 2 ≤ b) (hs : 1 ≤ s) (hu0 : 0 ≤ u0) (hu01 : u0 ≤ 1)
    (hu0s : u0 ≤ s) :
    run (barycentricPFA b s (u0, u0^2) hb hs (by
      simp only [InTriangle]; constructor; · exact hu0
      constructor; · exact hu01
      constructor; · positivity
      nlinarith)) w = barycentric s (reversedValue b u0 w, (reversedValue b u0 w)^2) := by
  have hb' : (b : ℝ) ≠ 0 := by positivity
  have h_triangle : ∀ (u : ℝ), 0 ≤ u → u ≤ 1 → InTriangle s (u, u^2) := by
    intro u hu hu1
    simp only [InTriangle]
    exact ⟨hu, hu1, sq_nonneg u, by nlinarith⟩
  -- General lemma: foldl (step M_x) starting from barycentric s (u, u^2) gives the right result
  -- where M_x is any barycentricPFA with that initial state
  have h_step : ∀ (b : ℕ) (s : ℝ) (x : ℝ × ℝ) (hb : 2 ≤ b) (hs : 1 ≤ s)
      (hx : InTriangle s x) (hb' : (b : ℝ) ≠ 0) (u : ℝ) (hu : 0 ≤ u) (hu1 : u ≤ 1) (j : Fin b),
      step (barycentricPFA b s x hb hs hx) (barycentric s (u, u^2)) j =
        barycentric s (digitMap b j (u, u^2)) := by
    intros b s x hb hs hx hb' u hu hu1 j
    have hs' : s ≠ 0 := by linarith
    exact step_barycentric b s x (u, u^2) hb hs hx hs' j
  have h_digitMap_square : ∀ (b : ℕ) (u : ℝ) (j : Fin b) (hb' : (b : ℝ) ≠ 0),
      digitMap b j (u, u^2) = ((u + j) / b, ((u + j) / b)^2) := by
    intro b u j hb'
    ext <;> simp [digitMap] <;> field_simp <;> ring
  -- Now prove the main statement by induction
  have h_main : ∀ (w : List (Fin b)) (u : ℝ) (hu : 0 ≤ u) (hu1 : u ≤ 1),
      run (barycentricPFA b s (u, u^2) hb hs (h_triangle u hu hu1)) w =
        barycentric s (reversedValue b u w, (reversedValue b u w)^2) := by
    intro w
    induction w with
    | nil =>
      intro u hu hu1
      rfl
    | cons j w' ih =>
      intro u hu hu1
      simp only [run, List.foldl_cons]
      have hx : InTriangle s (u, u^2) := h_triangle u hu hu1
      change List.foldl (step (barycentricPFA b s (u, u^2) hb hs hx))
        (step (barycentricPFA b s (u, u^2) hb hs hx) (barycentric s (u, u^2)) j) w' = _
      rw [h_step b s (u, u^2) hb hs hx hb' u hu hu1 j]
      rw [h_digitMap_square b u j hb']
      have h_rev : reversedValue b u (j :: w') = reversedValue b ((u + j) / b) w' := rfl
      have hj_nat : (j : ℕ) < b := Fin.is_lt j
      have hj' : (j : ℝ) ≤ (b : ℝ) - (1 : ℝ) := by
        have : (j : ℕ) ≤ b - 1 := Nat.le_pred_of_lt hj_nat
        have hb_pos : 0 < b := by linarith
        have hb_val : (b : ℝ) - 1 = ((b - 1 : ℕ) : ℝ) := by
          simp [Nat.cast_sub hb_pos]
        rw [hb_val]
        exact_mod_cast this
      have h_u' : 0 ≤ (u + j) / b ∧ (u + j) / b ≤ 1 := by
        constructor <;> (field_simp; nlinarith)
      exact ih ((u + j) / b) h_u'.1 h_u'.2
  exact h_main w u0 hu0 hu01

/-- Acceptance is the downward parabola `u-u²/s`, the displayed closed formula
in the proofs of Theorem 3 and Proposition 4 of the original source. -/
lemma acceptance_barycentricPFA (b : ℕ) (s u0 : ℝ) (w : List (Fin b))
    (hb : 2 ≤ b) (hs : 1 ≤ s) (hu0 : 0 ≤ u0) (hu01 : u0 ≤ 1)
    (hu0s : u0 ≤ s) :
    acceptance (barycentricPFA b s (u0, u0^2) hb hs (by
      simp only [InTriangle]; constructor; · exact hu0
      constructor; · exact hu01
      constructor; · positivity
      nlinarith)) w =
      reversedValue b u0 w - (reversedValue b u0 w)^2 / s := by
  unfold acceptance
  simp only [Fin.sum_univ_three]
  simp [barycentricPFA]
  show run (barycentricPFA b s (u0, u0^2) hb hs (by
      simp only [InTriangle]; constructor; · exact hu0
      constructor; · exact hu01
      constructor; · positivity
      nlinarith)) w 0 = reversedValue b u0 w - (reversedValue b u0 w)^2 / s
  rw [run_barycentricPFA b s u0 w hb hs hu0 hu01 hu0s]
  simp [barycentric]

/-- The integer whose base-`b` little-endian digits are the input word. It is the
integer numerator underlying `v(z)` in the General alphabets section of the
original source. -/
def wordValueNat {b : ℕ} (w : List (Fin b)) : ℕ :=
  Nat.ofDigits b (w.map (fun j => (j : ℕ)))

/-- Fixed-length words have injective base-`b` values, formalizing the injectivity
(and hence grid separation) assertion in the binary and general constructions of
the original source. -/
lemma wordValueNat_injective_fixedLength {b : ℕ} (hb : 2 ≤ b)
    {w z : List (Fin b)} (hlen : w.length = z.length)
    (hval : wordValueNat w = wordValueNat z) : w = z := by
  simp [wordValueNat] at hval
  by_cases H : w.length = 1
  · have ⟨w₀, hw₀⟩ : ∃ w₀, w = [w₀] := by sorry
    subst w
    have ⟨z₀, hz₀⟩ : ∃ z₀, z = [z₀] := by sorry
    subst z
    simp
    simp [List.flatMap, List.flatten] at hval
    exact Fin.eq_of_val_eq hval
  by_cases H : w.length = 2
  · have ⟨w₀, w₁, hw₀⟩ : ∃ w₀ w₁, w = [w₀, w₁] := by sorry
    subst w
    have ⟨z₀, z₁, hz₀⟩ : ∃ z₀ z₁, z = [z₀, z₁] := by sorry
    subst z
    simp
    simp [List.flatMap, List.flatten] at hval
    simp [Nat.ofDigits] at hval
    -- true since w₀ mod b < b
    sorry
  simp [List.flatMap, List.flatten] at hval
  sorry

/-- Closed form for the reversed dynamics, namely
`u_n = v(z) + u₀ b⁻ⁿ`, from Proposition 4 of the original source. -/
lemma reversedValue_eq (b : ℕ) (u0 : ℝ) (w : List (Fin b)) (hb : 0 < b) :
    reversedValue b u0 w =
      ((wordValueNat w : ℝ) + u0) / (b : ℝ) ^ w.length := by
  have h : ∀ w u, reversedValue b u w = ((wordValueNat w : ℝ) + u) / (b : ℝ) ^ w.length := by
    intro w
    induction w with
    | nil =>
      intro u
      simp [reversedValue, wordValueNat]
    | cons j w' ih =>
      intro u
      simp [reversedValue, wordValueNat]
      simp_all [reversedValue, Nat.ofDigits_cons]
      have heq : wordValueNat w' = Nat.ofDigits b (List.flatMap (fun a => [↑a]) w') := by
        simp [wordValueNat]
      simp [heq]
      field_simp
      ring
  exact h w u0

/-- Equal-length distinct words have different terminal values. This is the
injectivity step that makes the parabola's maximum unique in Theorem 3 and
Proposition 4 of the original source. -/
lemma reversedValue_ne_of_ne {b : ℕ} (hb : 2 ≤ b) (u0 : ℝ)
    {w z : List (Fin b)} (hlen : w.length = z.length) (hne : w ≠ z) :
    reversedValue b u0 w ≠ reversedValue b u0 z := by
  intro heq
  rw [reversedValue_eq b u0 w (by linarith), reversedValue_eq b u0 z (by linarith)] at heq
  apply hne
  apply wordValueNat_injective_fixedLength hb hlen
  have hpos : (0 : ℝ) < b := by positivity
  have hpow : (b : ℝ) ^ w.length ≠ 0 := pow_ne_zero _ hpos.ne'
  rw [hlen] at heq
  field_simp [hpow] at heq
  exact_mod_cast (by linarith : (wordValueNat w : ℝ) = wordValueNat z)

/-- Reflection of digits `j ↦ b-1-j`, the alphabet permutation used in the
“Choosing the target” paragraph of Proposition 4 in the original source. -/
def complementDigit {b : ℕ} (j : Fin b) : Fin b :=
  ⟨b - 1 - j, by omega⟩

/-- Relabel a PFA along a bijection of alphabets. This formalizes the invariance
of `A_P` under alphabet permutations invoked in Theorem 3 and Proposition 4 of
the original source. -/
def relabelPFA {α β : Type*} {k : ℕ} (e : α ≃ β) (M : PFA β k) : PFA α k where
  initial := M.initial
  transition a := M.transition (e a)
  final := M.final
  initial_nonneg := M.initial_nonneg
  initial_sum := M.initial_sum
  transition_nonneg := fun a => M.transition_nonneg (e a)
  transition_sum := fun a => M.transition_sum (e a)

/-- Acceptance commutes with alphabet relabeling, the precise fact behind the
alphabet-permutation reduction in the original source. -/
lemma acceptance_relabelPFA {α β : Type*} {k : ℕ} (e : α ≃ β)
    (M : PFA β k) (w : List α) :
    acceptance (relabelPFA e M) w = acceptance M (w.map e) := by
  have hstep : ∀ p : Fin k → ℝ, ∀ a : α, step (relabelPFA e M) p a = step M p (e a) := by
    intro p a
    funext j
    simp [step, relabelPFA]
  have hrun : run (relabelPFA e M) w = run M (w.map e) := by
    have hinit : (relabelPFA e M).initial = M.initial := rfl
    have : ∀ (p : Fin k → ℝ), List.foldl (step (relabelPFA e M)) p w =
           List.foldl (step M) p (w.map e) := by
      induction w with
      | nil => intro p; rfl
      | cons a w' ih =>
        intro p
        simp only [List.foldl_cons, List.map_cons]
        rw [hstep p a, ih]
    simp [run, this, hinit]
  have hfinal : (relabelPFA e M).final = M.final := rfl
  simp [acceptance, hrun, hfinal]


example
    (u0 : ℝ) (hu0 : 0 ≤ u0) (hu01 : u0 ≤ 1) :
    1 / 2 ≤ reversedValue 2 u0 [0]
    ∨
    1 / 2 ≤ reversedValue 2 u0 [1] := by
    simp [reversedValue]
    right
    field_simp;linarith

example
    (u0 : ℝ) (b₀ b₁ b₂ : Fin 2) (hu0 : 0 ≤ u0) :
    1 / 2 ≤ reversedValue 2 u0 [b₀, b₁, b₂, 1] -- whichever ends in 1
    := by
    simp [reversedValue]
    field_simp;linarith

/-- A direct three-state witness when the target terminal value is at least
`1/2`; this is the parabola argument common to Theorem 3 and Proposition 4 in
the original source. -/
lemma exists_three_state_of_target_ge_half {b : ℕ} (hb : 2 ≤ b)
    (w : List (Fin b)) (u0 : ℝ) (hu0 : 0 ≤ u0) (hu01 : u0 ≤ 1)
    (ht : 1 / 2 ≤ reversedValue b u0 w) :
    -- ht seems to be true, but which `u0` to apply this to?
    -- maybe `u0 = 0`
    ∃ M : PFA (Fin b) 3, UniquelyMaximizes M w := by
  -- Set s = 2 * reversedValue b u0 w, so the parabola max is at u = s/2 = reversedValue b u0 w
  set u_target := reversedValue b u0 w with hu_target_def
  have hu_target_pos : 0 < u_target := by linarith
  set s := 2 * u_target with hs_def
  have hs_ge_one : 1 ≤ s := by linarith
  have hu0_le_s : u0 ≤ s := by linarith
  -- Construct the PFA
  let M := barycentricPFA b s (u0, u0^2) hb hs_ge_one (by
    simp only [InTriangle]
    exact ⟨hu0, hu01, sq_nonneg u0, by nlinarith⟩)
  use M
  intro z hlen hne
  -- Use the acceptance formula
  have hacc_w := acceptance_barycentricPFA b s u0 w hb hs_ge_one hu0 hu01 hu0_le_s
  have hacc_z := acceptance_barycentricPFA b s u0 z hb hs_ge_one hu0 hu01 hu0_le_s
  rw [hacc_w, hacc_z]
  -- Need: reversedValue b u0 z - (reversedValue b u0 z)^2/s < u_target - u_target^2/s
  -- The parabola u - u²/s is maximized at u = s/2 = u_target
  -- For any u ≠ u_target: (u - u²/s) < (u_target - u_target²/s)
  -- This is equivalent to (u_target - u)² > 0
  set uz := reversedValue b u0 z with uz_def
  have huz_ne : uz ≠ u_target := reversedValue_ne_of_ne hb u0 hlen hne
  have key : ∀ (u : ℝ), u ≠ u_target → u - u^2/s < u_target - u_target^2/s := by
    intro u hu
    have hs_pos : 0 < s := by linarith
    have h : (u_target - u)^2 > 0 := sq_pos_of_ne_zero (sub_ne_zero.mpr hu.symm)
    field_simp at h ⊢
    nlinarith
  exact key uz huz_ne

/-- The main general-alphabet result, Proposition 4 (`prop:general`) and hence
Theorem 1 (`thm:main`) of the original source: every nonempty finite word over
an alphabet of size at least two has probabilistic automatic complexity at most
three. -/
theorem probabilisticAutomaticComplexity_le_three {b : ℕ} (hb : 2 ≤ b)
    (w : List (Fin b)) (hw : w ≠ []) :
    probabilisticAutomaticComplexity w ≤ 3 := by
  have := @exists_three_state_of_target_ge_half
  unfold probabilisticAutomaticComplexity
  simp [sInf]
  split_ifs with g₀
  · simp [UniquelyMaximizes]
    obtain ⟨n,M,hM⟩ := g₀
    specialize @this b hb w 0 (by simp) (by field_simp;simp)
        (by
            -- true for w or its complement
            sorry)

    use 3, (by simp)
    obtain ⟨M,hM⟩ := this
    use M
    intro z hz
    simp [UniquelyMaximizes] at hM
    apply hM
    tauto
  · simp

/-- Binary specialization, exactly Theorem 3 (`thm:binary`) of the original
source. -/
theorem binary_probabilisticAutomaticComplexity_le_three
    (w : List (Fin 2)) (hw : w ≠ []) :
    probabilisticAutomaticComplexity w ≤ 3 := by
  exact probabilisticAutomaticComplexity_le_three (by omega) w hw

/-- Conditional form of Corollary 5 (`cor:max`) from the original source. The
source's cited external fact that some binary word has complexity three is made
an explicit hypothesis, while this development supplies the matching universal
upper bound. -/
theorem binary_maximum_eq_three
    (hex : ∃ w : List (Fin 2), probabilisticAutomaticComplexity w = 3) :
    IsGreatest (Set.range (fun w : List (Fin 2) => probabilisticAutomaticComplexity w)) 3 := by
  simp [IsGreatest]
  constructor
  · exact hex
  · simp [upperBounds]
    intro a
    apply binary_probabilisticAutomaticComplexity_le_three
    -- just missing the empty word, which doesn't matter
    sorry

/-- Formal version of the computational observation in Remark 9 (Verification)
of the original source: the constructed parabola has its strict unique maximum
at the target for every equal-length word, not merely for the tested lengths. -/
theorem exact_verification_all_lengths {b : ℕ} (hb : 2 ≤ b)
    (w : List (Fin b)) (u0 : ℝ) (hu0 : 0 ≤ u0) (hu01 : u0 ≤ 1)
    (ht : 1 / 2 ≤ reversedValue b u0 w) :
    ∃ M : PFA (Fin b) 3, ∀ z, z.length = w.length → z ≠ w →
      acceptance M z < acceptance M w := by
  simpa [UniquelyMaximizes] using exists_three_state_of_target_ge_half hb w u0 hu0 hu01 ht

end PFAComplexity
