import IntegrationSection6.NormalizedLiftDomains
import Section3.GammaProjection
import Section3.NormalizationSaturation

/-! Glue native definable local VF lifts over the original real base.
Finite Gamma representatives remain internal and only original names plus
that finite tuple enter the compactness bound. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section7
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {n : ℕ}
local notation "N" => (@CanonicalStructure.normalize M sM)

theorem exists_native_gamma_glued_lift {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (hreal : Cardinal.mk B.real < κ)
    (C : Set (Fin (n+n) → M)) (hC : DefinableOverBase B (fun _ => .rv) C)
    (hloc : ∀ z ∈ C, ∃ A : Set (Fin (n+n) → M),
      @Set.Definable M B.real LRV N (Fin (n+n)) A ∧ z ∈ rawLiftDomain A) :
    ∃ A : Set (Fin (n+n) → M), @Set.Definable M B.real LRV N (Fin (n+n)) A ∧ C ⊆ rawLiftDomain A := by
  obtain ⟨k,c,hc⟩ := hC.specialize
  let T := B.real ∪ Set.range (rawTuple c)
  have hCN : @Set.Definable M T LRV N (Fin (n+n)) C :=
    ((definableOver_iff_normalized_raw T (fun _ => .rv) C).mp hc).1
  have hlocN : ∀ z ∈ C, ∃ A : Set (Fin (n+n) → M),
      @Set.Definable M B.real LRV N (Fin (n+n)) A ∧ z ∈ @rawLiftDomain M N n A := by
    intro z hz
    obtain ⟨A,hA,hzA⟩ := hloc z hz
    exact ⟨A,hA,(Set.ext_iff.mp (rawLiftDomain_normalize A) z).mpr hzA⟩
  obtain ⟨A,hA,hgood⟩ := @exists_originalBase_gluedLift M N n κ hs.normalize B.real T
    Set.subset_union_left (small_union_range hκ B.real hreal (rawTuple c)) C hCN hlocN
  exact ⟨A,hA,fun z hz => (Set.ext_iff.mp (rawLiftDomain_normalize A) z).mp (hgood hz)⟩

end IntegrationInACVF.Section6
