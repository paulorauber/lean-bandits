/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Paulo Rauber
-/
import Mathlib.Probability.Kernel.Posterior
import LeanBandits.SequentialLearning.Algorithm
import LeanBandits.ForMathlib.MeasurableArgMax

open MeasureTheory ProbabilityTheory Finset
open Learning

variable {K : ℕ} (hK : 0 < K)

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [Nonempty Ω]
variable (μ : Measure Ω) [IsProbabilityMeasure μ]
variable (ℓ : Kernel (Ω × (Fin K)) ℝ) [IsMarkovKernel ℓ]

noncomputable
def tsStepLikelihood : Kernel Ω (Fin K × ℝ) := (Kernel.const _ (uniformOn Set.univ)) ⊗ₖ ℓ

instance isMarkovKernel_tsStepSlikelihood : IsMarkovKernel (tsStepLikelihood ℓ) := by
  haveI : Nonempty (Fin K) := Fin.pos_iff_nonempty.mp hK
  haveI : IsProbabilityMeasure (uniformOn (Set.univ : Set (Fin K))) :=
    uniformOn_isProbabilityMeasure Set.finite_univ Set.univ_nonempty
  unfold tsStepLikelihood
  infer_instance

noncomputable
def tsLikelihood : (n : ℕ) → Kernel Ω (Iic n → Fin K × ℝ)
  | 0 => (tsStepLikelihood ℓ).map (MeasurableEquiv.piUnique (fun _ : Iic 0 ↦ Fin K × ℝ)).symm
  | n + 1 => ((tsLikelihood n) ×ₖ (tsStepLikelihood ℓ)).map
    (MeasurableEquiv.IicSuccProd (fun _ ↦ Fin K × ℝ) n).symm

instance isMarkovKernel_tsLikelihood (n : ℕ) : IsMarkovKernel (tsLikelihood ℓ n) := by
  haveI := isMarkovKernel_tsStepSlikelihood hK ℓ
  induction n with
  | zero => exact Kernel.IsMarkovKernel.map _ (MeasurableEquiv.piUnique _).symm.measurable
  | succ n hk => exact Kernel.IsMarkovKernel.map _ (MeasurableEquiv.IicSuccProd _ _).symm.measurable

noncomputable
def tsPosterior (n : ℕ) : Kernel (Iic n → Fin K × ℝ) Ω :=
  haveI := isMarkovKernel_tsLikelihood hK ℓ n
  posterior (tsLikelihood ℓ n) μ

instance isMarkovKernel_tsPosterior (n : ℕ) : IsMarkovKernel (tsPosterior hK μ ℓ n) := by
  unfold tsPosterior
  infer_instance

noncomputable
def tsPolicy (n : ℕ) : Kernel (Iic n → Fin K × ℝ) (Fin K) :=
  have : Nonempty (Fin K) := Fin.pos_iff_nonempty.mp hK
  (tsPosterior hK μ ℓ n).map (measurableArgmax (fun ω k ↦ ∫ r, r ∂(ℓ (ω, k))))

instance isMarkovKernel_tsPolicy (n : ℕ) : IsMarkovKernel (tsPolicy hK μ ℓ n) := by
  have : Nonempty (Fin K) := Fin.pos_iff_nonempty.mp hK
  apply Kernel.IsMarkovKernel.map
  exact measurable_measurableArgmax fun k =>
    (stronglyMeasurable_id.integral_kernel (κ := ℓ.comap (·, k) (by fun_prop))).measurable

noncomputable
def tsInitialPolicy : Measure (Fin K) :=
  have : Nonempty (Fin K) := Fin.pos_iff_nonempty.mp hK
  μ.map (measurableArgmax (fun ω k ↦ ∫ r, r ∂(ℓ (ω, k))))

instance isProbabilityMeasure_tsInitialPolicy : IsProbabilityMeasure (tsInitialPolicy hK μ ℓ) := by
  have : Nonempty (Fin K) := Fin.pos_iff_nonempty.mp hK
  refine Measure.isProbabilityMeasure_map (measurable_measurableArgmax fun k => ?_).aemeasurable
  exact (stronglyMeasurable_id.integral_kernel (κ := ℓ.comap (·, k) (by fun_prop))).measurable

noncomputable
def tsAlgorithm : Algorithm (Fin K) ℝ where
  policy := tsPolicy hK μ ℓ
  h_policy := isMarkovKernel_tsPolicy hK μ ℓ
  p0 := tsInitialPolicy hK μ ℓ
  hp0 := isProbabilityMeasure_tsInitialPolicy hK μ ℓ
