import Integration7.GammaWeightedVolumeSchemata
import Integration7.VolumeSchemaCorrespondences
import Integration7.RVProductGammaBalance

/-! First-order Gamma-weight validity for an actual comparison-chart
formula. Its correspondence is derived from the source and target graphs. -/

set_option backward.isDefEq.respectTransparency false
noncomputable section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p a b k : ℕ} {sp : Fin p → SortTag}

def volumeChartGammaRowValid (F : GammaRVVolumeSchema B p a k sp)
    (G : GammaRVVolumeSchema B p b k sp) (H : Set (Fin ((p+a)+b) → M)) (z : Fin p → M) : Prop :=
  (∀ i, sortEval (sp i) (z i)) ∧
  ∀ r : Fin (((k+1)+1)+((k+1)+1)) → M,
    Fin.append z r ∈ schemaVolumeCorrespondence (weightedVolumeSchema F) (weightedVolumeSchema G) H →
      r ∈ rvProductGammaBalance (M := M) ((k+1)+1)

theorem volumeChartGammaRowValid_definable
    (hc : CanonicalStructure.IsCanonical (M := M))
    (F : GammaRVVolumeSchema B p a k sp) (G : GammaRVVolumeSchema B p b k sp)
    {H : Set (Fin ((p+a)+b) → M)}
    (hH : DefinableOverBase B (Fin.append (Fin.append sp (fun _ : Fin a => .rv)) (fun _ : Fin b => .rv)) H) :
    DefinableOverBase B sp {z | volumeChartGammaRowValid F G H z} := by
  let d := (k+1)+1
  let st := Fin.append sp (fun _ : Fin (d+d) => SortTag.rv)
  let C := schemaVolumeCorrespondence (weightedVolumeSchema F) (weightedVolumeSchema G) H
  have hC : DefinableOverBase B st C :=
    schemaVolumeCorrespondence_definable (weightedVolumeSchema F) (weightedVolumeSchema G) hH
  let D : Set (Fin (p+(d+d)) → M) :=
    {w | w ∘ Fin.natAdd p ∈ rvProductGammaBalance (M := M) d ∧ w ∈ sortedUniverse st}
  have hD : DefinableOverBase B st D := (rvProductGammaBalance_definable hc B d).preimage_real st (Fin.natAdd p)
  have h := gamma_family_row_subset_definable sp (fun _ : Fin (d+d) => .rv) hC hD
  convert h using 1
  ext z
  constructor
  · rintro ⟨hz,hvalid⟩
    refine ⟨hz,?_⟩
    intro r hr
    have he : Fin.append z r ∘ Fin.natAdd p = r := funext (Fin.append_right _ _)
    exact ⟨he.symm ▸ hvalid r hr,hC.proper _ hr⟩
  · rintro ⟨hz,hvalid⟩
    refine ⟨hz,?_⟩
    intro r hr
    have hmem := (hvalid r hr).1
    have he : Fin.append z r ∘ Fin.natAdd p = r := funext (Fin.append_right _ _)
    exact he ▸ hmem

theorem volumeChartGammaRowValid_apply
    (F : GammaRVVolumeSchema B p a k sp) (G : GammaRVVolumeSchema B p b k sp)
    (H : Set (Fin ((p+a)+b) → M)) (z : Fin p → M) (hz : volumeChartGammaRowValid F G H z)
    (u v : Fin ((k+1)+1) → M) (hu : ∀ i, iRV (u i)) (hv : ∀ i, iRV (v i))
    (x : Fin a → M) (y : Fin b → M)
    (hx : Fin.append (Fin.append z x) u ∈ weightedVolumeGraph F)
    (hxy : Fin.append (Fin.append z x) y ∈ H)
    (hy : Fin.append (Fin.append z y) v ∈ weightedVolumeGraph G) :
    Fin.append u v ∈ rvProductGammaBalance (M := M) ((k+1)+1) := by
  apply hz.2 (Fin.append u v)
  exact (schemaVolumeCorrespondence_append (weightedVolumeSchema F) (weightedVolumeSchema G) H z u v
    hz.1 hu hv).mpr ⟨x,y,hx,hxy,hy⟩

end IntegrationInACVF.Section7
