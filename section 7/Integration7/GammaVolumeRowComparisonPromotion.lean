import Integration7.GammaVolumeComparisonPromotion

/-! Promote a comparison while retaining given source and target volume
schemata exactly. This is the interface needed by finite common-witness
assembly, where endpoint schemata have already been fixed. -/

set_option backward.isDefEq.respectTransparency false
noncomputable section
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4
open SpecialTransformations.Section5 (Point GammaGraphDefinable)
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p q k : ℕ} {sp : Fin p → SortTag} {sq : Fin q → SortTag}

theorem gamma_volume_row_comparison_promotion {κ : Cardinal}
    (hc : CanonicalStructure.IsCanonical (M := M))
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hreal : Cardinal.mk B.real < κ) (hgamma : Cardinal.mk B.gamma < κ)
    (C : BaseContext M) (z : Fin p → M) (y : Fin q → M)
    (hz : ∀ i, sortEval (sp i) (z i)) (hy : ∀ i, sortEval (sq i) (y i))
    (hBase : (C.base : Set M) = (Substructure.closure LRV (B.real ∪ Set.range (Fin.append z y)) : Set M))
    {U V : PositiveRVVolumeObject (M := M) (C.base : Set M) k}
    (F : GammaRVVolumeSchema B p U.underlying.obj.arity k sp)
    (G : GammaRVVolumeSchema B p V.underlying.obj.arity k sp)
    (hF : F.valid z) (hG : G.valid z) (P : RVVolumeSchemaRow U F z) (Q : RVVolumeSchemaRow V G z)
    (e : RVVolumeIso U V)
    (hGraph : GammaGraphDefinable ⟨B.real ∪ Set.range z,B.gamma⟩
      (fun (x : Point (M := M) 0 U.underlying.obj.arity) (y : Point (M := M) 0 V.underlying.obj.arity) =>
        ∃ u : U.essential.obj.domain, u.val = x.2 ∧ (finiteIsoMap e.iso u).val = y.2)) :
    ∃ W : GammaRVVolumeIsoCertificateSchema B p U.underlying.obj.arity V.underlying.obj.arity k sp,
      W.source = F ∧ W.target = G ∧ W.valid z ∧
      ∀ x y, Fin.append (Fin.append z x) y ∈ W.chart ↔
        ∃ u : U.essential.obj.domain, rvValues u.val = x ∧ rvValues (finiteIsoMap e.iso u).val = y := by
  obtain ⟨H,hH,hHz⟩ := gamma_volume_chart_promotion z hz e.iso hGraph
  obtain ⟨A,D,j,hj,g,_,hg,_,hA⟩ := e.exists_bounded_weight_label_certificate hc C
  obtain ⟨E,hE,hErow⟩ := finite_auxiliary_map_promotion hc hκ hs hreal hgamma C z y hz hy hBase D g hg
  let W : GammaRVVolumeIsoCertificateSchema B p U.underlying.obj.arity V.underlying.obj.arity k sp := {
    source := F
    target := G
    chart := H
    chart_definable := hH
    supports := A
    extraArity := q
    extraSort := sq
    exceptionDegree := j
    exceptionDegree_lt := hj
    exception := E }
  have hErow' : ∀ w : Fin ((k+1)+1) → CanonicalRV.RVSort M,
      w ∈ D.carrier ↔ Fin.append (Fin.append z y) (rvValues w) ∈ E.domain := hErow
  have hW : W.valid z := GammaRVVolumeIsoCertificateSchema.valid_of_rows
    W z hF hG P Q e hHz y hE D.carrier hErow' hA
  exact ⟨W,rfl,rfl,hW,hHz⟩

end IntegrationInACVF.Section7
