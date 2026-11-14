import Integration7.TermContextGammaGraphs
import Integration7.GammaVolumeRowComparisonPromotion

/-! Every actual volume comparison over the original named term context
promotes. Full chart definability follows by parameter descent. -/

set_option backward.isDefEq.respectTransparency false
noncomputable section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4

namespace IntegrationInACVF.Section7

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p k : ℕ} {sp : Fin p → SortTag}

theorem gamma_volume_actual_comparison_promotion {κ : Cardinal}
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hreal : Cardinal.mk B.real < κ) (hgamma : Cardinal.mk B.gamma < κ)
    (z : Fin p → M) (hz : ∀ i, sortEval (sp i) (z i))
    (hBase : (C.base : Set M) = (Substructure.closure LRV (B.real ∪ Set.range z) : Set M))
    {U V : PositiveRVVolumeObject (M := M) (C.base : Set M) k}
    (F : GammaRVVolumeSchema B p U.underlying.obj.arity k sp)
    (G : GammaRVVolumeSchema B p V.underlying.obj.arity k sp)
    (hF : F.valid z) (hG : G.valid z) (P : RVVolumeSchemaRow U F z) (Q : RVVolumeSchemaRow V G z)
    (e : RVVolumeIso U V) :
    ∃ W : GammaRVVolumeIsoCertificateSchema B p U.underlying.obj.arity V.underlying.obj.arity k sp,
      W.source = F ∧ W.target = G ∧ W.valid z ∧
      ∀ x y, Fin.append (Fin.append z x) y ∈ W.chart ↔
        ∃ u : U.essential.obj.domain, rvValues u.val = x ∧ rvValues (finiteIsoMap e.iso u).val = y := by
  have hGraph := gammaGraph_of_termContext hc C ⟨B.real ∪ Set.range z,B.gamma⟩ hBase
    (finiteIsoMap e.iso).graph_definable
  have he : Fin.append z (Fin.elim0 : Fin 0 → M) = z := by
    funext i
    exact Fin.append_left z Fin.elim0 i
  have hBase' : (C.base : Set M) =
      (Substructure.closure LRV (B.real ∪ Set.range (Fin.append z (Fin.elim0 : Fin 0 → M))) : Set M) := by
    rw [he]
    exact hBase
  exact gamma_volume_row_comparison_promotion (sq := fun i : Fin 0 => i.elim0)
    hc hκ hs hreal hgamma C z Fin.elim0 hz (fun i => i.elim0) hBase'
    F G hF hG P Q e hGraph

end IntegrationInACVF.Section7
