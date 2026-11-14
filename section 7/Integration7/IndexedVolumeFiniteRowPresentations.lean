import Integration7.GammaVolumeIndexedPresentations
import Integration7.GammaVolumeElementaryDensities
import Integration7.GammaVolumeCoproductDensities
import IntegrationSection6.GammaSchemaFiniteRowPresentations

/-! Indexed volume presentations need finite row maps and functional
density graphs. Their existence is independent of a chosen numeric bound
in a coproduct or elementary formula template. -/

set_option backward.isDefEq.respectTransparency false
noncomputable section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4
open SpecialTransformations.Section5 (RV)
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p a b d k : ℕ}
variable {T : Set (Fin p → RV (M := M))}
variable {R : (Fin p → RV (M := M)) → (Fin d → RV (M := M)) → Prop}

theorem GammaRVVolumeSchema.exists_indexedVolumePresentation_finiteRows
    (F : GammaRVVolumeSchema B p a k (fun _ => .rv))
    (BP : GammaFiniteGraphPresentation B p d T R)
    (hFinite : ∀ t ∈ T, F.object.finiteRow (rvValues t))
    (hDensity : ∀ t ∈ T, functionMapRowValid (fun _ => .rv) F.object.domain F.density (rvValues t)) :
    Nonempty (F.IndexedPresentation BP) := by
  let P := F.object.indexedPresentation_finiteRows BP hFinite
  have hUnique (t : T) (x : F.object.rowDomain (rvValues t.val)) :
      ∃! ω : Fin 1 → RV (M := M), F.rowDensity (rvValues t.val) x.val ω := by
    obtain ⟨v,hv,hu⟩ := (hDensity t.val t.property).2.1 (rvValues x.val) x.property
    have hSort (i : Fin 1) : iRV (v i) := by
      simpa only [Fin.append_right,sortEval,iRV] using F.density_definable.proper _ hv (Fin.natAdd (p+a) i)
    exact ⟨fun i => ⟨v i,hSort i⟩,hv,fun ω hω => rvValues_injective (hu (rvValues ω) hω)⟩
  apply exists_gammaVolumeGraphPresentation P (F.indexedDensity_graph BP)
  · intro w
    obtain ⟨ω,hω,hu⟩ := hUnique ⟨indexedLeft w.val,w.property.1⟩ ⟨indexedRight w.val,w.property.2⟩
    exact ⟨ω,⟨w.property,hω⟩,fun ω' hω' => hu ω' hω'.2⟩
  · intro w ω h
    exact h.1
  · intro w ω h
    exact F.rowDensity_nonzero _ _ _ h.2

def GammaRVVolumeSchema.indexedVolumePresentation_finiteRows
    (F : GammaRVVolumeSchema B p a k (fun _ => .rv))
    (BP : GammaFiniteGraphPresentation B p d T R)
    (hFinite : ∀ t ∈ T, F.object.finiteRow (rvValues t))
    (hDensity : ∀ t ∈ T, functionMapRowValid (fun _ => .rv) F.object.domain F.density (rvValues t)) :
    F.IndexedPresentation BP :=
  Classical.choice (F.exists_indexedVolumePresentation_finiteRows BP hFinite hDensity)

def GammaRVVolumeSchema.indexedCoprodPresentation
    (F : GammaRVVolumeSchema B p a k (fun _ => .rv))
    (G : GammaRVVolumeSchema B p b k (fun _ => .rv))
    (BP : GammaFiniteGraphPresentation B p d T R)
    (hF : ∀ t ∈ T, F.valid (rvValues t)) (hG : ∀ t ∈ T, G.valid (rvValues t)) :
    (F.coprodFormula G).IndexedPresentation BP :=
  (F.coprodFormula G).indexedVolumePresentation_finiteRows BP
    (fun t ht => F.object.finiteRow_coprod G.object _ (fun i => (t i).property)
      (F.object.finiteRow_of_valid _ (hF t ht).1) (G.object.finiteRow_of_valid _ (hG t ht).1))
    (fun t ht => F.coprod_density_valid G _ (hF t ht) (hG t ht))

end IntegrationInACVF.Section7
