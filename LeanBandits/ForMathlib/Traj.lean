import Mathlib.Probability.Kernel.IonescuTulcea.Traj

open Filter Finset Function MeasurableEquiv MeasurableSpace MeasureTheory Preorder ProbabilityTheory

variable {X : ℕ → Type*} [∀ n, MeasurableSpace (X n)]
variable {κ : (n : ℕ) → Kernel (Π i : Iic n, X i) (X (n + 1))} [∀ n, IsMarkovKernel (κ n)]

namespace ProbabilityTheory.Kernel

lemma traj_zero_map_eval_zero :
    (Kernel.traj κ 0).map (fun h ↦ h 0)
      = Kernel.deterministic (MeasurableEquiv.piUnique _)
        (MeasurableEquiv.piUnique _).measurable := by
  have h1 : (fun h : (n : ℕ) → X n => h 0) =
      (fun f : (i : Iic (0:ℕ)) → X i => f ⟨0, mem_Iic.mpr (le_refl 0)⟩) ∘
        frestrictLe (π := X) 0 := by
    funext f; simp only [Function.comp_apply, frestrictLe, restrict]
  have h2 : (fun f : (i : Iic (0:ℕ)) → X i => f ⟨0, mem_Iic.mpr (le_refl 0)⟩) =
      MeasurableEquiv.piUnique (fun i : Iic (0:ℕ) => X i) := by
    funext f; simp only [MeasurableEquiv.piUnique_apply]; rfl
  calc (Kernel.traj κ 0).map (fun h ↦ h 0)
      = (Kernel.traj κ 0).map ((fun f => f ⟨0, _⟩) ∘ frestrictLe (π := X) 0) := by rw [h1]
    _ = ((Kernel.traj κ 0).map (frestrictLe 0)).map (fun f => f ⟨0, _⟩) := by
        rw [Kernel.map_comp_right _ (by fun_prop) (by fun_prop)]
    _ = (Kernel.partialTraj κ 0 0).map (fun f => f ⟨0, _⟩) := by rw [Kernel.traj_map_frestrictLe]
    _ = (Kernel.deterministic (frestrictLe₂ (le_refl 0)) (by fun_prop)).map
          (fun f => f ⟨0, _⟩) := by rw [Kernel.partialTraj_zero]
    _ = Kernel.deterministic ((fun f => f ⟨0, _⟩) ∘ frestrictLe₂ (le_refl 0)) (by fun_prop) := by
        rw [Kernel.deterministic_map _ (by fun_prop)]
    _ = Kernel.deterministic (MeasurableEquiv.piUnique _) _ := by congr 1

end ProbabilityTheory.Kernel
