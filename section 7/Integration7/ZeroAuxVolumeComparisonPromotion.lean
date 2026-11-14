import Integration7.ActualVolumeComparisonPromotion
import Integration7.ZeroAuxVolumeWitnesses

/-! Promotion over the original named term context needs no additional
exception-parameter block. The stronger conclusion records this fact. -/

set_option backward.isDefEq.respectTransparency false
noncomputable section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p k : ℕ} {sp : Fin p → SortTag}

theorem gamma_volume_comparison_promotion_no_auxiliary {κ : Cardinal}
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
      W.extraArity = 0 ∧ W.source = F ∧ W.target = G ∧ W.valid z ∧
      ∀ x y, Fin.append (Fin.append z x) y ∈ W.chart ↔
        ∃ u : U.essential.obj.domain, rvValues u.val = x ∧ rvValues (finiteIsoMap e.iso u).val = y := by
  have hGraph := gammaGraph_of_termContext hc C ⟨B.real ∪ Set.range z,B.gamma⟩ hBase
    (finiteIsoMap e.iso).graph_definable
  have he : Fin.append z (Fin.elim0 : Fin 0 → M) = z := funext (Fin.append_left z Fin.elim0)
  have hBase' : (C.base : Set M) =
      (Substructure.closure LRV (B.real ∪ Set.range (Fin.append z (Fin.elim0 : Fin 0 → M))) : Set M) := by
    rw [he]
    exact hBase
  obtain ⟨H,hH,hHz⟩ := gamma_volume_chart_promotion z hz e.iso hGraph
  obtain ⟨A,D,j,hj,g,_,hg,_,hA⟩ := e.exists_bounded_weight_label_certificate hc C
  obtain ⟨E,hE,hErow⟩ := finite_auxiliary_map_promotion (sq := fun i : Fin 0 => i.elim0)
    hc hκ hs hreal hgamma C z Fin.elim0 hz (fun i => i.elim0) hBase' D g hg
  let W : GammaRVVolumeIsoCertificateSchema B p U.underlying.obj.arity V.underlying.obj.arity k sp := {
    source := F
    target := G
    chart := H
    chart_definable := hH
    supports := A
    extraArity := 0
    extraSort := Fin.elim0
    exceptionDegree := j
    exceptionDegree_lt := hj
    exception := E }
  have hErow' : ∀ w : Fin ((k+1)+1) → CanonicalRV.RVSort M,
      w ∈ D.carrier ↔ Fin.append (Fin.append z (Fin.elim0 : Fin 0 → M)) (rvValues w) ∈ E.domain := hErow
  exact ⟨W,rfl,rfl,rfl,GammaRVVolumeIsoCertificateSchema.valid_of_rows W z hF hG P Q e hHz
    Fin.elim0 hE D.carrier hErow' hA,hHz⟩

end IntegrationInACVF.Section7
