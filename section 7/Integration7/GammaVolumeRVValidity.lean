import Integration7.WeightedJacobianFormulas
import Integration7.GammaVolumeGammaValidity

/-! First-order supported RV-Jacobian validity off an explicitly coded
exception on source coordinate-and-density labels. -/

set_option backward.isDefEq.respectTransparency false
noncomputable section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section9
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p a b k j : ℕ} {sp : Fin p → SortTag}

def supportedSchemaJacobianFormula (F : GammaRVVolumeSchema B p a k sp)
    (G : GammaRVVolumeSchema B p b k sp) (H : Set (Fin ((p+a)+b) → M))
    (A : Finset (VolumeChartSupport (k+1))) : Set (Fin (p+(((k+1)+1)+((k+1)+1))) → M) :=
  weightedJacobianFormula sp {w | ∃ σ ∈ A,
    w ∈ tupleVolumeChartGraph σ (schemaVolumeCorrespondence F.object G.object H)}

theorem supportedSchemaJacobianFormula_definable
    (hc : CanonicalStructure.IsCanonical (M := M))
    (F : GammaRVVolumeSchema B p a k sp) (G : GammaRVVolumeSchema B p b k sp)
    {H : Set (Fin ((p+a)+b) → M)}
    (hH : DefinableOverBase B (Fin.append (Fin.append sp (fun _ : Fin a => .rv)) (fun _ : Fin b => .rv)) H)
    (A : Finset (VolumeChartSupport (k+1))) :
    DefinableOverBase B (Fin.append sp (fun _ : Fin (((k+1)+1)+((k+1)+1)) => .rv))
      (supportedSchemaJacobianFormula F G H A) :=
  weightedJacobianFormula_definable hc sp
    (gamma_tupleVolumeChartGraphUnion_definable hc A sp (schemaVolumeCorrespondence_definable F.object G.object hH))

def weightedPairSourceIndices (p d : ℕ) : Fin (p+(d+1)) → Fin (p+((d+1)+(d+1))) :=
  Fin.addCases (Fin.castAdd ((d+1)+(d+1))) (fun i => Fin.natAdd p (Fin.castAdd (d+1) i))

def weightedPairsOutsideException (F : GammaRVVolumeSchema B p a k sp)
    (G : GammaRVVolumeSchema B p b k sp) (H : Set (Fin ((p+a)+b) → M))
    (E : GammaFiniteRVSchema B p ((k+1)+1) j sp) : Set (Fin (p+(((k+1)+1)+((k+1)+1))) → M) :=
  {w | w ∈ schemaVolumeCorrespondence (weightedVolumeSchema F) (weightedVolumeSchema G) H ∧
    w ∘ weightedPairSourceIndices p (k+1) ∉ E.domain}

theorem weightedPairsOutsideException_definable
    (F : GammaRVVolumeSchema B p a k sp) (G : GammaRVVolumeSchema B p b k sp)
    {H : Set (Fin ((p+a)+b) → M)}
    (hH : DefinableOverBase B (Fin.append (Fin.append sp (fun _ : Fin a => .rv)) (fun _ : Fin b => .rv)) H)
    (E : GammaFiniteRVSchema B p ((k+1)+1) j sp) :
    DefinableOverBase B (Fin.append sp (fun _ : Fin (((k+1)+1)+((k+1)+1)) => .rv))
      (weightedPairsOutsideException F G H E) := by
  let st := Fin.append sp (fun _ : Fin (((k+1)+1)+((k+1)+1)) => SortTag.rv)
  have hC := schemaVolumeCorrespondence_definable (weightedVolumeSchema F) (weightedVolumeSchema G) hH
  have hE := E.domain_definable.preimage_real st (weightedPairSourceIndices p (k+1))
  have h := hC.inter hE.compl
  convert h using 1
  ext w
  change (_ ∧ _ ∉ E.domain) ↔ (_ ∧ w ∈ sortedUniverse st ∧ ¬(_ ∈ E.domain ∧ w ∈ sortedUniverse st))
  exact ⟨fun h => ⟨h.1,hC.proper w h.1,fun he => h.2 he.1⟩,
    fun h => ⟨h.1,fun he => h.2.2 ⟨he,h.2.1⟩⟩⟩

def volumeChartRVRowValid (F : GammaRVVolumeSchema B p a k sp)
    (G : GammaRVVolumeSchema B p b k sp) (H : Set (Fin ((p+a)+b) → M))
    (A : Finset (VolumeChartSupport (k+1))) (E : GammaFiniteRVSchema B p ((k+1)+1) j sp)
    (z : Fin p → M) : Prop :=
  (∀ i, sortEval (sp i) (z i)) ∧
  ∀ r : Fin (((k+1)+1)+((k+1)+1)) → M,
    Fin.append z r ∈ weightedPairsOutsideException F G H E →
      Fin.append z r ∈ supportedSchemaJacobianFormula F G H A

theorem volumeChartRVRowValid_definable
    (hc : CanonicalStructure.IsCanonical (M := M))
    (F : GammaRVVolumeSchema B p a k sp) (G : GammaRVVolumeSchema B p b k sp)
    {H : Set (Fin ((p+a)+b) → M)}
    (hH : DefinableOverBase B (Fin.append (Fin.append sp (fun _ : Fin a => .rv)) (fun _ : Fin b => .rv)) H)
    (A : Finset (VolumeChartSupport (k+1))) (E : GammaFiniteRVSchema B p ((k+1)+1) j sp) :
    DefinableOverBase B sp {z | volumeChartRVRowValid F G H A E z} :=
  gamma_family_row_subset_definable sp _ (weightedPairsOutsideException_definable F G hH E)
    (supportedSchemaJacobianFormula_definable hc F G hH A)

end IntegrationInACVF.Section7
