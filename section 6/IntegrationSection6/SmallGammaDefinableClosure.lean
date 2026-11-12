import IntegrationSection6.SmallDefinableSingletons
import Section3.GammaFullDescent
import Section3.GammaGoodRelations
import Section3.ParameterBridge

/-! Definable closure of a small real/Gamma base remains small. The proof
counts formulas over the original names, including one fixed representative
per original Gamma name; it never bounds an internal RV code universe. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem closureBase_real_small {κ : Cardinal} (hκ : Cardinal.aleph0 < κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hg : Cardinal.mk B.gamma < κ) :
    Cardinal.mk (closureBase B).real < κ := by
  apply small_definable_singletons hκ (commonRealNames B) (closureBase B).real
    (commonRealNames_small hκ.le B hr hg)
  rintro x ⟨σ,hx⟩
  exact hx.common_names.raw_definable

theorem closureBase_gamma_small {κ : Cardinal} (hκ : Cardinal.aleph0 < κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hg : Cardinal.mk B.gamma < κ) :
    Cardinal.mk (closureBase B).gamma < κ := by
  apply small_injective_definable_sets hκ (commonRealNames B)
    (fun γ : (closureBase B).gamma => Values.gammaPullback {γ.val})
    (commonRealNames_small hκ.le B hr hg)
  · intro γ δ he
    apply Subtype.ext
    have hm : raw (representative γ.val) ∈ Values.gammaPullback {γ.val} :=
      (mem_gammaPullback_code _ _).mpr (by simp only [representative_value,Set.mem_singleton_iff])
    change Values.gammaPullback {γ.val} = Values.gammaPullback {δ.val} at he
    rw [he] at hm
    have h := (mem_gammaPullback_code {δ.val} (representative γ.val)).mp hm
    simpa only [Set.mem_singleton_iff,representative_value] using h
  · intro γ
    exact γ.property.common_names.raw_definable

end IntegrationInACVF.Section6
