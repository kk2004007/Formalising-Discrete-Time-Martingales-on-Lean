module
/-
Copyright (c) 2026 Karthikeya Kakarlapudi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Karthikeya Kakarlapudi CID: 02406947
-/
public import Mathlib
open MeasureTheory ProbabilityTheory
open scoped ENNReal

@[expose] public section

/-!
# PROJECT 1 Formalisation of Discrete Time Martingale Theory

In this file we introduce discrete time martingales and formalise
the Martingale Transform Theorem

## Main results
- `martingales`: a construction of a `martingales`, given a `filtration` and a `Measure`.
- `martingaleransform` : the product of a  `previsible` process and an `adapted` process.
- `martingaletransformtheorem`: the main transform theorem of martingales

## Notation

 - `Ω` : Sample Space.
 - `ω` : Elements of Sample Space / Events
 - `m`, `𝓕`: Measurable Spaces/ σ-algebras over `Ω`
 - `X`, `H` : Processes on the measurable spaces `m` and `𝓕`,
 usually martingales and previsible process respectively
 - `μ` : Measure over `m` and `𝓕`,
 usually refers to Expectation and Conditional Expectation

## References
* https://leansearch.net/?q=measure+theory
* Mathlib4 GitHub
* https://leanprover-community.github.io/blog/posts/basic-probability-in-mathlib/
-/
variable {Ω : Type*} {m : MeasurableSpace Ω} (X : ℕ → Ω → ℝ)
/- We will not be using MeasureTheory.Martingale to ensure
we build the theory of discrete time martingales from scratch
-/
-- Type* is useful in picking a suitable type universe rather than declaring one immediately
/-- A filtration is an increasing sequence of σ-algebras `(Fi)∞ i=1` that are all subsets
of `F`, that is `F1 ⊂F2 ⊂F3 ⊂···⊂Fn ⊂···⊂F`. -/
structure filtration (Ω : Type*) [m : MeasurableSpace Ω] where
-- Properties of filtration
-- Sequence of σ-algebras
  seq : ℕ → MeasurableSpace Ω
--Monotonic property of the sequence of σ-algebras
  monotoneincr : Monotone seq
--All the members of the monotonic sequence of σ-algebras are subsets of m
  subsetsin : ∀ i : ℕ, seq i ≤ m
--Note that measurable spaces is Mathlib convention for σ-algebras
attribute [coe] filtration.seq
-- to ensure filtration can be called upon as an instance
instance : CoeFun (filtration Ω ) fun _ => ℕ → MeasurableSpace Ω :=
  ⟨fun f => f.seq⟩

/-- We say a sequence `(Xi)∞ i=1` of random variables is adapted
to the filtration `f` if `Xi` is `Fi`-measurable for each `i`. -/
def adapted (f : filtration Ω) : Prop :=
  ∀ i : ℕ, Measurable[f i] (X i)

variable {X} in
/-- This lemma states that the negative of an adapted process is adapted -/
lemma adapted.neg {𝓕 : filtration Ω} (hXAdapted : adapted X 𝓕) :
  adapted (-X) 𝓕 := by
  unfold adapted
  unfold adapted at hXAdapted
  intro i
  exact (hXAdapted i).neg

/-- X_neg is short hand for negative of a random process of
to avoid defining a function each time -/
def X_neg (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω):= -X n ω

/-- Condexp_martingale is an definition to concise and clean up the notation
for `μ[X (i + 1) | 𝓕 i]` -/
noncomputable def condexp_martingale (μ : Measure Ω) (𝓕 : filtration Ω) (X : ℕ → Ω → ℝ) (i : ℕ)
:= μ[X (i + 1) | 𝓕 i]

/-- Let `(𝓕i)∞ i=1` be a filtration and `(Xi)∞ i=1` be a sequence of random variables
adapted to the filtration. We say `(Xi)∞ i=1` is a martingale for the filtration
`(𝓕i)∞ i=1` if, for each `i`, both of the following properties hold:
1.`E[|Xi|] <∞`
2. `E[Xi+1|Fi] = Xi` -/
structure martingales (𝓕 : filtration Ω) (μ : Measure Ω) where
  martingalesAdapted : adapted X 𝓕
  martingalesIntegrable : ∀ i, Integrable (X i) μ
  martingaleproperty {i : ℕ} : condexp_martingale μ 𝓕 X i =ᵐ[μ] X i

/-- Let `(𝓕i)∞ i=1` be a filtration and `(Xi)∞ i=1` be a sequence of random variables
adapted to the filtration. We say `(Xi)∞ i=1` is a supermartingale for the filtration
`(𝓕i)∞ i=1` if, for each `i`, both of the following properties hold:
1.`E[|Xi|] < ∞`
2. `E[Xi+1|Fi] ≤ Xi` -/
structure supermartingales (X : ℕ → Ω → ℝ) (𝓕 : filtration Ω) (μ : Measure Ω) where
  supermartingalesAdapted : adapted X 𝓕
  supermartingalesIntegrable : ∀ i, Integrable (X i) μ
  supermartingaleproperty {i : ℕ} : condexp_martingale μ 𝓕 X i ≤ᵐ[μ] X i

/-- Let `(𝓕i)∞ i=1` be a filtration and `(Xi)∞ i=1` be a sequence of random variables
adapted to the filtration. We say (Xi)∞ i=1 is a submartingale for the filtration
`(𝓕i)∞ i=1` if, for each `i`, both of the following properties hold:
1.`E[|Xi|] < ∞`
2. `E[Xi+1|Fi] ≥ Xi` -/
structure submartingales (𝓕 : filtration Ω) (μ : Measure Ω) where
  submartingalesAdapted : adapted X 𝓕
  submartingalesIntegrable : ∀ i, Integrable (X i) μ
  submartingaleproperty {i : ℕ} : X i ≤ᵐ[μ] condexp_martingale μ 𝓕 X i

/-- Given a filtration `𝓕`, a sequence `(Xi)∞ i=1` of random variables
is called previsible if `X(i+1)` is `𝓕i`-measurable for each `i`. -/
def previsible (X : ℕ → Ω → ℝ) (𝓕 : filtration Ω) : Prop :=
  ∀ i : ℕ, Measurable[𝓕 i] (X (i+1))

/-- Let `(Xi)∞ i=1` be adapted to the filtration `(Fi)∞ i=1`.
Let `(Hi)∞ i=1` be previsible to the same filtration.
We then define a new sequence `((H •X)i)∞ i=1`
by `(H•X)i = ∑︁n k=1 hk(Xk−Xk−1)`.
`((H•X)i)∞ i=1` is called the martingale transform of `(Xi)∞i=1` by `(Hi)∞ i=1` -/
def MartingaleTransform (H X : ℕ → Ω → ℝ) (n : ℕ) : Ω → ℝ :=
  ∑ k ∈ Finset.Icc (1) (n), H (k) * (X (k) - X (k - 1))

/-- Lemma stating the adapted and previsible properties of the martingale transform
by triviality -/
lemma Martingale_Transform_Property (𝓕 : filtration Ω) (H X : ℕ → Ω → ℝ)
    (_hX : adapted X 𝓕)
    (_hH : previsible H 𝓕) :
    True := by
  trivial

/-- Lemma stating that the negative of the submartingale is a supermartingale. -/
lemma submartingaleisnegativesupermartingale
    (μ : Measure Ω) (𝓕 : filtration Ω) (X : ℕ → Ω → ℝ) (hX : submartingales X 𝓕 μ) :
    supermartingales (-X) 𝓕 μ where
  supermartingalesAdapted := by
    apply adapted.neg
    exact hX.submartingalesAdapted
  supermartingalesIntegrable := by
    intro i
    exact (hX.submartingalesIntegrable i).neg
  supermartingaleproperty := by
    intro i
    have hNegatedInequality : (fun ω => -(condexp_martingale μ 𝓕 X i ω)) ≤ᵐ[μ]
    (fun ω => -X i ω) := by
      filter_upwards [(hX.submartingaleproperty)] with ω hω
      exact neg_le_neg hω
    have hCE : condexp_martingale μ 𝓕 (X_neg X) i =ᵐ[μ] - condexp_martingale μ 𝓕 X i :=
      MeasureTheory.condExp_neg (X (i + 1)) (𝓕 i)
    calc
      condexp_martingale μ 𝓕 (X_neg X) i
      ≤ᵐ[μ] -condexp_martingale μ 𝓕 X i := hCE.le
  _ ≤ᵐ[μ] -X i := hNegatedInequality

/-- Lemma stating that the negative of the supermartingale is a submartingale. -/
lemma supermartingaleisnegativesubmartingale
    {Ω : Type*} {m : MeasurableSpace Ω} (μ : Measure Ω) (𝓕 : filtration Ω)
    (X : ℕ → Ω → ℝ) (hX : supermartingales X 𝓕 μ) :
    submartingales (-X) 𝓕 μ where
  submartingalesAdapted := by
      apply adapted.neg
      exact hX.supermartingalesAdapted
  submartingalesIntegrable := by
    intro i
    exact (hX.supermartingalesIntegrable i).neg
  submartingaleproperty := by
    intro i
    have hInequality : condexp_martingale μ 𝓕 X i ≤ᵐ[μ] X i := (hX.supermartingaleproperty)
    have hNegatedInequality :
    (fun ω => -X i ω) ≤ᵐ[μ] (fun ω => -(condexp_martingale μ 𝓕 X i ω)) := by
      filter_upwards [hInequality] with ω hω
      exact neg_le_neg hω
    calc
      (fun n ω => -X n ω) i
      ≤ᵐ[μ] (fun ω => -(condexp_martingale μ 𝓕 X i  ω)) := hNegatedInequality
    _ =ᵐ[μ] condexp_martingale μ 𝓕 (X_neg X) i := by
       symm
       exact MeasureTheory.condExp_neg (X (i + 1)) (𝓕 i)

/-- Lemma stating that a random process that is both a supermartingale
and a submartingale is a martingale. -/
lemma supermartingaleandsubmartingalesimpliesmartingale
    (μ : Measure Ω) (𝓕 : filtration Ω) (X : ℕ → Ω → ℝ)
    (hsupermartingale : supermartingales X 𝓕 μ)
    (hsubmartingale : submartingales X 𝓕 μ) :
    martingales X 𝓕 μ where
  martingalesAdapted := by
    exact hsupermartingale.supermartingalesAdapted
  martingalesIntegrable := by
    intro i
    exact (hsupermartingale.supermartingalesIntegrable i)
  martingaleproperty := by
    intro i
    exact (hsubmartingale.submartingaleproperty.antisymm
      hsupermartingale.supermartingaleproperty).symm

/-- Lemma stating that given `martingale transform` `(H • X)∞ i=1`,
we have `(H • X)i+1 = (H • X)i + Hi+1(X(i+1)-Xi)` -/
lemma martingaleTransform_succ (H X : ℕ → Ω → ℝ) (i : ℕ) :
MartingaleTransform H X (i + 1) = MartingaleTransform H X i + H (i + 1) * (X (i + 1) - X i) := by
  unfold MartingaleTransform
  ext ω
  simp only [Finset.sum_apply, Pi.add_apply, Pi.mul_apply, Pi.sub_apply]
  rw [Finset.sum_Icc_succ_top (by omega)]
  simp

/-- Lemma stating that given `martingale transform` `(H • X)∞ i=1`,
  we have `E[H(i+1) (X(i+1)-Xi) | Fi] = 0` -/
lemma martingaleTransform_increment_condExp
(H X : ℕ → Ω → ℝ) (hXmartingale : martingales X 𝓕 μ)
(hHprevisible : previsible H 𝓕) (hHbounded : ∀ i : ℕ, ∃ C : ℝ, ∀ ω : Ω, |H i ω| ≤ C)
(hμσfinite : ∀ i : ℕ, SigmaFinite (μ.trim (𝓕.subsetsin i))) (i : ℕ) :
μ[fun ω => H (i + 1) ω * (X (i + 1) ω - X i ω) | 𝓕 i] =ᵐ[μ] 0 := by
  have hdiff : Integrable (X (i + 1) - X i) μ :=
  (hXmartingale.martingalesIntegrable (i+1)).sub (hXmartingale.martingalesIntegrable i)
  have hHmeas : Measurable[𝓕 i] (H (i + 1)) := hHprevisible i
  have hHstrong : StronglyMeasurable[𝓕 i] (H (i + 1)) := hHmeas.stronglyMeasurable
  have hf : Integrable (X (i + 1) : Ω → ℝ) μ := hXmartingale.martingalesIntegrable (i + 1)
  have hg : Integrable (X i : Ω → ℝ) μ := hXmartingale.martingalesIntegrable i
  have hcond : μ[X (i + 1) - X i | 𝓕 i] =ᵐ[μ] μ[X (i + 1) | 𝓕 i] - μ[X i | 𝓕 i] := by
    exact MeasureTheory.condExp_sub (m₀ := m) (μ := μ) (E := ℝ) hf hg (𝓕 i)
  have hproduct : Integrable (fun ω => H (i + 1) ω * (X (i + 1) ω - X i ω)) μ := by
    obtain ⟨C, hC⟩ := hHbounded (i + 1)
    have hHambient : Measurable (H (i + 1)) := Measurable.mono hHmeas (𝓕.subsetsin i) le_rfl
    have hHae : AEStronglyMeasurable (H (i + 1)) μ := hHambient.aestronglyMeasurable
    have hbound : ∀ᵐ ω ∂μ, ‖H (i + 1) ω‖ ≤ C := by
      filter_upwards [] with ω
      simpa [Real.norm_eq_abs] using hC ω
    exact hdiff.bdd_mul hHae hbound
  have hpullout : μ[fun ω => H (i + 1) ω * (X (i + 1) ω - X i ω) | 𝓕 i]
  =ᵐ[μ] H (i + 1) * μ[X (i + 1) - X i | 𝓕 i] := by
    change μ[H (i + 1) * (X (i + 1) - X i) | 𝓕 i] =ᵐ[μ] H (i + 1) * μ[X (i + 1) - X i | 𝓕 i]
    exact MeasureTheory.condExp_mul_of_stronglyMeasurable_left
      (m := 𝓕 i) (mΩ := m) (μ := μ) (hf := hHstrong) (hfg := hproduct) (hg := hdiff)
  have hXi_meas : Measurable[𝓕 i] (X i) := hXmartingale.martingalesAdapted i
  have hXi_strong : StronglyMeasurable[𝓕 i] (X i) := hXi_meas.stronglyMeasurable
  have hXi_cond : μ[X i | 𝓕 i] =ᵐ[μ] X i := by
    let : SigmaFinite (μ.trim (𝓕.subsetsin i)) := hμσfinite i
    have hXi_eq : μ[X i | 𝓕 i] = X i := MeasureTheory.condExp_of_stronglyMeasurable
      (𝓕.subsetsin i) hXi_strong hg
    exact Filter.Eventually.of_forall (fun ω => congrFun hXi_eq ω)
  have hzero : μ[X (i + 1) - X i | 𝓕 i] =ᵐ[μ] 0 := by
    have hmart : μ[X (i + 1) | 𝓕 i] =ᵐ[μ] X i := by
      change condexp_martingale μ 𝓕 X i =ᵐ[μ] X i
      exact hXmartingale.martingaleproperty
    filter_upwards [hcond, hmart, hXi_cond] with ω hdiff hmart hXi
    have hpoint : μ[X (i + 1) | 𝓕 i] ω - μ[X i | 𝓕 i] ω = 0 := by
      rw [hmart, hXi]
      ring
    calc
      μ[X (i + 1) - X i | 𝓕 i] ω
            = μ[X (i + 1) | 𝓕 i] ω - μ[X i | 𝓕 i] ω := hdiff
      _ = 0 := hpoint
  calc
    μ[fun ω => H (i + 1) ω *
        (X (i + 1) ω - X i ω) | 𝓕 i]
        =ᵐ[μ] H (i + 1) * μ[X (i + 1) - X i | 𝓕 i] :=
          hpullout
    _ =ᵐ[μ] H (i + 1) * 0 := by
      filter_upwards [hzero] with ω hω
      simpa using
      congrArg (fun x : ℝ => H (i + 1) ω * x) hω
  filter_upwards [] with ω
  simp

/-- Lemma stating that the martingale transform `(H • X)∞ i=1`
is adapted to the filtration `(𝓕i)∞ i=1` -/
lemma martingaleTransform_adapted
(𝓕 : filtration Ω) (H X : ℕ → Ω → ℝ) (hXmartingale : martingales X 𝓕 μ)
(hHprevisible : previsible H 𝓕) : adapted (MartingaleTransform H X) 𝓕 := by
  have hXAdapted : adapted X 𝓕 := hXmartingale.martingalesAdapted
  unfold MartingaleTransform
  unfold adapted
  unfold adapted at hXAdapted
  unfold previsible at hHprevisible
  have hHMeasurable : ∀ (i : ℕ), Measurable[𝓕 i] (H (i + 1)) := hHprevisible
  intro i
  have hsum : Measurable[𝓕 i] (fun ω => ∑ k ∈ Finset.Icc 1 i, H k ω * (X k ω - X (k - 1) ω))
  := by
    apply Finset.measurable_sum
    intro k hk
    rcases Finset.mem_Icc.mp hk with ⟨hk_lower, hk_upper⟩
    have hk_prev : k - 1 ≤ i := le_trans (Nat.sub_le k 1) hk_upper
    have hHk : Measurable[𝓕 i] (H k) := by
      have hHprev : Measurable[𝓕 (k - 1)] (H k) := by
        simpa [Nat.sub_add_cancel hk_lower] using hHMeasurable (k - 1)
      exact Measurable.mono hHprev (𝓕.monotoneincr hk_prev) le_rfl
    have hXk : Measurable[𝓕 i] (X k) :=
    Measurable.mono (hXAdapted k) (𝓕.monotoneincr hk_upper) le_rfl
    have hXprev : Measurable[𝓕 i] (X (k - 1)) :=
    Measurable.mono (hXAdapted (k - 1)) (𝓕.monotoneincr hk_prev) le_rfl
    exact hHk.mul (hXk.sub hXprev)
  convert hsum using 1
  ext ω
  simp

/-- Lemma stating that the martingale transform `(H • X)∞ i=1`
is integrable with respect to the filtration `(𝓕i)∞ i=1` -/
lemma martingaleTransform_integrable
(𝓕 : filtration Ω) (H X : ℕ → Ω → ℝ) (hXmartingale : martingales X 𝓕 μ)
(hHprevisible : previsible H 𝓕) (hHbounded : ∀ i : ℕ, ∃ C : ℝ, ∀ ω : Ω, |H i ω| ≤ C)
: ∀ (i : ℕ), Integrable (MartingaleTransform H X i) μ := by
  intro i
  unfold MartingaleTransform
  have hsum : Integrable (fun ω => ∑ k ∈ Finset.Icc 1 i, H k ω * (X k ω - X (k - 1) ω)) μ := by
    apply MeasureTheory.integrable_finsetSum
      (s := Finset.Icc 1 i) (f := fun k ω => H k ω * (X k ω - X (k - 1) ω))
    intro k hk
    have hk_lower : 1 ≤ k := (Finset.mem_Icc.mp hk).1
    have hXdiff : Integrable (X k - X (k - 1)) μ :=
    (hXmartingale.martingalesIntegrable k).sub (hXmartingale.martingalesIntegrable (k - 1))
    have hHmeas : Measurable (H k) := by
      have h := hHprevisible (k - 1)
      rw [Nat.sub_add_cancel hk_lower] at h
      exact Measurable.mono h (𝓕.subsetsin (k - 1)) le_rfl
    have hHae : AEStronglyMeasurable (H k) μ := hHmeas.aestronglyMeasurable
    obtain ⟨C, hC⟩ := hHbounded k
    have hHbound : ∀ᵐ ω ∂μ, ‖H k ω‖ ≤ C := by
      filter_upwards [] with ω
      simpa [Real.norm_eq_abs] using hC ω
    exact MeasureTheory.Integrable.bdd_mul hXdiff hHae hHbound
  apply MeasureTheory.Integrable.congr hsum
  filter_upwards [] with ω
  simp only [Finset.sum_apply]
  simp only [Pi.mul_apply, Pi.sub_apply]

/-- Suppose that (Xi)∞ i=1 is a martingale for the filtration (𝓕i)∞ i=1
and (Hi)∞ i=1 is a previsible process with each Hi bounded.
Then, the sequence ((H•X)i)∞ i=1 is a martingale for the filtration (𝓕i)∞ i=1. -/
theorem martingaletransformtheorem
{Ω : Type*} {m : MeasurableSpace Ω} (μ : Measure Ω) (𝓕 : filtration Ω)
(H X : ℕ → Ω → ℝ) (hXmartingale : martingales X 𝓕 μ) (hHprevisible : previsible H 𝓕)
(hHbounded : ∀ i : ℕ, ∃ C : ℝ, ∀ ω : Ω, |H i ω| ≤ C)
(hμσfinite : ∀ i : ℕ, SigmaFinite (μ.trim (𝓕.subsetsin i))) :
martingales (MartingaleTransform (H) (X)) 𝓕 μ where
martingalesAdapted := by
  apply martingaleTransform_adapted
  · exact hXmartingale
  exact hHprevisible
martingalesIntegrable := by
  apply martingaleTransform_integrable
  · exact hXmartingale
  · exact hHprevisible
  exact hHbounded
martingaleproperty := by
  intro i
  let T := MartingaleTransform H X
  let D := fun ω => H (i + 1) ω * (X (i + 1) ω - X i ω)
  have hTi : Integrable (T i) μ := martingaleTransform_integrable 𝓕 H X hXmartingale
      hHprevisible hHbounded i
  have hTmeas : Measurable[𝓕 i] (T i) := martingaleTransform_adapted 𝓕 H X hXmartingale
      hHprevisible i
  have hTstrong : StronglyMeasurable[𝓕 i] (T i) := hTmeas.stronglyMeasurable
  have hDint : Integrable D μ := by
    have hdiff : Integrable (X (i + 1) - X i) μ := (hXmartingale.martingalesIntegrable (i + 1)).sub
        (hXmartingale.martingalesIntegrable i)
    obtain ⟨C, hC⟩ := hHbounded (i + 1)
    have hHmeas : Measurable (H (i + 1)) := Measurable.mono (hHprevisible i) (𝓕.subsetsin i) le_rfl
    have hHae : AEStronglyMeasurable (H (i + 1)) μ := hHmeas.aestronglyMeasurable
    have hbound : ∀ᵐ ω ∂μ, ‖H (i + 1) ω‖ ≤ C := by
      filter_upwards [] with ω
      simpa [Real.norm_eq_abs] using hC ω
    change Integrable
      (fun ω => H (i + 1) ω * (X (i + 1) ω - X i ω)) μ
    exact hdiff.bdd_mul hHae hbound
  have hTcond : μ[T i | 𝓕 i] =ᵐ[μ] T i := by
    let  : SigmaFinite (μ.trim (𝓕.subsetsin i)) := hμσfinite i
    have hT_eq : μ[T i | 𝓕 i] = T i := MeasureTheory.condExp_of_stronglyMeasurable
      (𝓕.subsetsin i) hTstrong hTi
    exact Filter.Eventually.of_forall (fun ω => congrFun hT_eq ω)
  have hDcond : μ[D | 𝓕 i] =ᵐ[μ] 0 := by
    exact martingaleTransform_increment_condExp H X hXmartingale hHprevisible hHbounded
      hμσfinite i
  have hsumcond : μ[T i + D | 𝓕 i] =ᵐ[μ] μ[T i | 𝓕 i] + μ[D | 𝓕 i] := by
    exact MeasureTheory.condExp_add hTi hDint (𝓕 i)
  have hsucc : T (i + 1) = T i + D := by
    exact martingaleTransform_succ H X i
  change μ[T (i + 1) | 𝓕 i] =ᵐ[μ] T i
  calc
    μ[T (i + 1) | 𝓕 i] =ᵐ[μ] μ[T i + D | 𝓕 i] := by
          rw [hsucc]
    _ =ᵐ[μ] μ[T i | 𝓕 i] + μ[D | 𝓕 i] :=
          hsumcond
    _ =ᵐ[μ] T i + 0 := by
      filter_upwards [hTcond, hDcond] with ω hT hD
      change μ[T i | 𝓕 i] ω + μ[D | 𝓕 i] ω = T i ω + 0
      rw [hT, hD]
      simp
    _ =ᵐ[μ] T i := by
          filter_upwards [] with ω
          simp
