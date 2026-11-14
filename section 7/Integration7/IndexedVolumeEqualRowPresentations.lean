import Integration7.IndexedVolumeFiniteRowPresentations
import Integration7.GammaVolumeSchemaRowEquality

/-! Equal complete rows transfer functional density and finite-map
semantics, allowing indexed presentations without changing numeric bounds. -/

set_option backward.isDefEq.respectTransparency false
noncomputable section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4
open SpecialTransformations.Section5 (RV)
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p a d k : ℕ} {sp : Fin p → SortTag}

theorem GammaRVVolumeSchema.density_valid_of_sameRow
    (F G : GammaRVVolumeSchema B p a k sp) {z : Fin p → M} (h : F.sameRow G z)
    (hF : functionMapRowValid sp F.object.domain F.density z) :
    functionMapRowValid sp G.object.domain G.density z := by
  refine ⟨hF.1,?_,?_⟩
  · intro x hx
    obtain ⟨y,hy,hu⟩ := hF.2.1 x ((h.1.2.1 x).mpr hx)
    exact ⟨y,(h.2.2.2 x y).mp hy,fun y' hy' => hu y' ((h.2.2.2 x y').mpr hy')⟩
  · intro x y hy
    exact (h.1.2.1 x).mp (hF.2.2 x y ((h.2.2.2 x y).mpr hy))

def GammaRVVolumeSchema.indexedPresentation_of_sameRow
    {T : Set (Fin p → RV (M := M))}
    {R : (Fin p → RV (M := M)) → (Fin d → RV (M := M)) → Prop}
    (F G : GammaRVVolumeSchema B p a k (fun _ => .rv))
    (BP : GammaFiniteGraphPresentation B p d T R)
    (hF : ∀ t ∈ T, F.valid (rvValues t))
    (hEq : ∀ t ∈ T, F.sameRow G (rvValues t)) : G.IndexedPresentation BP :=
  G.indexedVolumePresentation_finiteRows BP
    (fun t ht => (F.object.finiteRow_congr G.object _ (hEq t ht).1).mp
      (F.object.finiteRow_of_valid _ (hF t ht).1))
    (fun t ht => F.density_valid_of_sameRow G (hEq t ht) (hF t ht).2)

end IntegrationInACVF.Section7
