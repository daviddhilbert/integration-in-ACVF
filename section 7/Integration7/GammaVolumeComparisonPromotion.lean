import Integration7.FiniteAuxiliaryMapPromotion
import Integration7.PromotedVolumeSchemaRows
import Integration7.GammaVolumeChartPromotion
import Integration7.VolumeCertificateRowRecognition

/-! Promote an actual original-Gamma volume comparison in a named
term-generated context. Auxiliary parameters encode its finite exception
map only; both volume objects and the full comparison chart retain the
original real/Gamma base and the original parameter tuple. -/

set_option backward.isDefEq.respectTransparency false
noncomputable section
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4
open SpecialTransformations.Section5 (Point RV GammaGraphDefinable)
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p q a b k : ℕ} {sp : Fin p → SortTag} {sq : Fin q → SortTag}

theorem gamma_volume_comparison_promotion {κ : Cardinal}
    (hc : CanonicalStructure.IsCanonical (M := M))
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hreal : Cardinal.mk B.real < κ) (hgamma : Cardinal.mk B.gamma < κ)
    (C : BaseContext M) (z : Fin p → M) (y : Fin q → M)
    (hz : ∀ i, sortEval (sp i) (z i)) (hy : ∀ i, sortEval (sq i) (y i))
    (hBase : (C.base : Set M) = (Substructure.closure LRV (B.real ∪ Set.range (Fin.append z y)) : Set M))
    {D : Set (Fin a → RV (M := M))} {E : Set (Fin b → RV (M := M))}
    {R : (Fin a → RV (M := M)) → (Fin (k+1) → RV (M := M)) → Prop}
    {T : (Fin b → RV (M := M)) → (Fin (k+1) → RV (M := M)) → Prop}
    {W : (Fin a → RV (M := M)) → (Fin 1 → RV (M := M)) → Prop}
    {Z : (Fin b → RV (M := M)) → (Fin 1 → RV (M := M)) → Prop}
    (P : GammaVolumeGraphPresentation ⟨B.real ∪ Set.range z,B.gamma⟩ a (k+1) D R W)
    (Q : GammaVolumeGraphPresentation ⟨B.real ∪ Set.range z,B.gamma⟩ b (k+1) E T Z)
    (hP : P.finite.codes ⊆ (C.base : Set M)) (hQ : Q.finite.codes ⊆ (C.base : Set M))
    (e : RVVolumeIso (P.inContext hc C hP).toObject (Q.inContext hc C hQ).toObject)
    (hGraph : GammaGraphDefinable ⟨B.real ∪ Set.range z,B.gamma⟩
      (fun (x : Point (M := M) 0 a) (y : Point (M := M) 0 b) =>
        ∃ u : (P.inContext hc C hP).toObject.essential.obj.domain,
          u.val = x.2 ∧ (finiteIsoMap e.iso u).val = y.2)) :
    ∃ F : GammaRVVolumeIsoCertificateSchema B p a b k sp, F.valid z ∧
      RVVolumeSchemaRow (P.inContext hc C hP).toObject F.source z ∧
      RVVolumeSchemaRow (Q.inContext hc C hQ).toObject F.target z ∧
      ∀ x y, Fin.append (Fin.append z x) y ∈ F.chart ↔
        ∃ u : (P.inContext hc C hP).toObject.essential.obj.domain,
          rvValues u.val = x ∧ rvValues (finiteIsoMap e.iso u).val = y := by
  obtain ⟨F,hF,hPF⟩ := gamma_volume_object_promotion_rows hc C hκ hs hreal hgamma z hz P hP
  obtain ⟨G,hG,hQG⟩ := gamma_volume_object_promotion_rows hc C hκ hs hreal hgamma z hz Q hQ
  obtain ⟨H,hH,hHz⟩ := gamma_volume_chart_promotion z hz e.iso hGraph
  obtain ⟨A,K,j,hj,g,_,hg,_,hA⟩ := e.exists_bounded_weight_label_certificate hc C
  obtain ⟨X,hX,hXrow⟩ := finite_auxiliary_map_promotion hc hκ hs hreal hgamma C z y hz hy hBase K g hg
  let Cmp : GammaRVVolumeIsoCertificateSchema B p a b k sp := {
    source := F
    target := G
    chart := H
    chart_definable := hH
    supports := A
    extraArity := q
    extraSort := sq
    exceptionDegree := j
    exceptionDegree_lt := hj
    exception := X }
  have hXrow' : ∀ w : Fin ((k+1)+1) → CanonicalRV.RVSort M,
      w ∈ K.carrier ↔ Fin.append (Fin.append z y) (rvValues w) ∈ X.domain := hXrow
  have hValid : Cmp.valid z := GammaRVVolumeIsoCertificateSchema.valid_of_rows
    Cmp z hF hG hPF hQG e hHz y hX K.carrier hXrow' hA
  exact ⟨Cmp,hValid,hPF,hQG,hHz⟩

end IntegrationInACVF.Section7
