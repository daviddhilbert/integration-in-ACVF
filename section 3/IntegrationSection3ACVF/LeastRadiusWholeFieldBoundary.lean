import IntegrationSection3ACVF.LinearRadiusThreshold

/-! Independent boundary check for existence of a least linear radius.
The numbered3.17 exclusion takes a given least-radius function; this
checks why its existence cannot be claimed for VF without allowing the
separate bottom radius. It does not contradict that conditional exclusion. -/

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open IntegrationInACVF.Section3

namespace IntegrationInACVF.Section3ACVF.LeastRadiusWholeFieldBoundary

open LinearRadiusThreshold

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem identity_graph (B : FullBaseAtomicity.Base (M := M)) :
    FullBaseAtomicity.OverBase B (ImaginaryBaseImages.graphOn {z : M | iVF z} id) := by
  have hVF := ((@definableAt_iff_normalized_raw M sM hM B.real .vf _).mp
    (@definableAt_sort M sM B.real .vf)).1
  have hD : FullBaseAtomicity.OverBase B {z : Fin 1 → M | iVF (z 0)} :=
    FullBaseAtomicity.OverBase.of_real hVF
  have hEq : FullBaseAtomicity.OverBase B {z : Fin 2 → M | z 1 = z 0} := by
    apply FullBaseAtomicity.OverBase.of_real
    letI := @CanonicalStructure.normalize M sM
    exact RawClosure.definable_equal_coordinates B.real 1 0
  exact FullBaseAtomicity.OverBase.inter
    (FullBaseAtomicity.OverBase.preimage_comp hD (fun _ : Fin 1 => (0 : Fin 2))) hEq

theorem identity_linear_at_gamma (x : VFType (M := M)) (γ : Values.Gamma (M := M)) :
    LinearOnRadius {z : M | iVF z} id (fun _ hz => hz) x γ.val := by
  have hSub : ballAt x γ.val ⊆ {z : M | iVF z} := by
    rw [ballAt_gamma x γ]
    intro y hy
    exact hy.1
  refine ⟨hSub,1,?_⟩
  intro y z hy hz
  change Values.vfValueHom (z-y) = (1 : Values.Gamma (M := M)).val * Values.vfValueHom (z-y)
  rw [Values.gamma_val_one,one_mul]

theorem no_least_radius (x : VFType (M := M)) :
    ¬ ∃ r : Values.GammaTop (M := M), IsLeastLinearRadius {z : M | iVF z} id (fun _ hz => hz) x r := by
  rintro ⟨r,hr⟩
  by_cases hInf : r = Values.infinity
  · have hLe := hr.2 (identity_linear_at_gamma x (1 : Values.Gamma (M := M)))
    rw [hInf] at hLe
    exact (1 : Values.Gamma (M := M)).property
      (le_antisymm (Values.le_infinity _) hLe)
  · let γ : Values.Gamma (M := M) := ⟨r,hInf⟩
    obtain ⟨β,hβγ⟩ := exists_lt γ
    have hLe := hr.2 (identity_linear_at_gamma x β)
    exact (not_lt_of_ge hLe) hβγ

end IntegrationInACVF.Section3ACVF.LeastRadiusWholeFieldBoundary
