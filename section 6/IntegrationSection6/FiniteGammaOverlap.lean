import IntegrationSection6.FiniteGammaLocusBlowups
import IntegrationSection6.FiniteGammaComplementSplits

/-! The actual four-piece overlap refinement, with original-Gamma charts
and finite volume on every subobject. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
namespace IntegrationInACVF.Section6.FiniteRV
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

variable {B : Base (M := M)} {S : Set M} {n : ℕ}
local notation "N" => (@CanonicalStructure.normalize M sM)
local notation "hN" => (@CanonicalStructure.normalized_model M sM hM)
variable {κ : Cardinal} {hκ : Cardinal.aleph0 ≤ κ} {hs : Saturated M κ}

variable {h00 : M ⊨ Axioms.ACVF00} {hsmall : Cardinal.mk B.real < κ}

variable {U V W : GammaObjectAt B S n}

structure GammaOverlapRefinementAt
    (H : GammaLocusBlowupAt hκ hs h00 hsmall  U V)
    (G : GammaLocusBlowupAt hκ hs h00 hsmall  U W) where
  left : @SpecialTransformations.DefinableGeometry.DefSet LRV M N (@rawRVSpace M N (rvObjectArity H.center.object.obj)) S
  left_subset : (@SpecialTransformations.DefinableGeometry.DefSet.carrier LRV M N _ S left) ⊆
    (@SpecialTransformations.DefinableGeometry.DefSet.carrier LRV M N _ S (rvObjectDomain H.center.object.obj))
  left_graph : GammaSetDefinable B {p : Point (M := M) 0 (rvObjectArity H.center.object.obj) |
    p.2 ∈ @SpecialTransformations.DefinableGeometry.DefSet.carrier LRV M N _ S left}
  right : @SpecialTransformations.DefinableGeometry.DefSet LRV M N (@rawRVSpace M N (rvObjectArity G.center.object.obj)) S
  right_subset : (@SpecialTransformations.DefinableGeometry.DefSet.carrier LRV M N _ S right) ⊆
    (@SpecialTransformations.DefinableGeometry.DefSet.carrier LRV M N _ S (rvObjectDomain G.center.object.obj))
  right_graph : GammaSetDefinable B {p : Point (M := M) 0 (rvObjectArity G.center.object.obj) |
    p.2 ∈ @SpecialTransformations.DefinableGeometry.DefSet.carrier LRV M N _ S right}
  overlap : GammaIsoAt (gammaRestrictAt H.center left left_subset left_graph)
    (gammaRestrictAt G.center right right_subset right_graph)
  exterior : GammaObjectAt B S n
  left_remainder : GammaIsoAt (gammaComplementAt U H.locus H.locus_graph)
    (gammaCoprodAt (gammaComplementAt G.center right right_graph) exterior)
  right_remainder : GammaIsoAt (gammaComplementAt U G.locus G.locus_graph)
    (gammaCoprodAt (gammaComplementAt H.center left left_graph) exterior)

def gammaOverlapRefinementAt
    (H : GammaLocusBlowupAt hκ hs h00 hsmall  U V)
    (G : GammaLocusBlowupAt hκ hs h00 hsmall  U W) : GammaOverlapRefinementAt H G := by
  let L := gammaLogicInput B
  let O := @SpecialTransformations.DefinableGeometry.DefSet.inter LRV M N _ S H.locus G.locus
  have hOΓ := L.inter H.locus_graph G.locus_graph
  let A := gammaRestrictAt U H.locus H.contained H.locus_graph
  let C := gammaRestrictAt U G.locus G.contained G.locus_graph
  have hoh : (@SpecialTransformations.DefinableGeometry.DefSet.carrier LRV M N _ S O) ⊆
      (@SpecialTransformations.DefinableGeometry.DefSet.carrier LRV M N _ S (rvObjectDomain A.object.obj)) := fun _ h => h.1
  have hog : (@SpecialTransformations.DefinableGeometry.DefSet.carrier LRV M N _ S O) ⊆
      (@SpecialTransformations.DefinableGeometry.DefSet.carrier LRV M N _ S (rvObjectDomain C.object.obj)) := fun _ h => h.2
  let eh := isoAtAmbient H.chart.symm.iso
  let eg := isoAtAmbient G.chart.symm.iso
  let X := @subobjectImage M N S n A.object.obj H.center.object.obj eh O hoh
  let Y := @subobjectImage M N S n C.object.obj G.center.object.obj eg O hog
  have hX := @subobjectImage_subset M N hN S n A.object.obj H.center.object.obj eh O hoh
  have hY := @subobjectImage_subset M N hN S n C.object.obj G.center.object.obj eg O hog
  have hXΓ := gamma_subobjectImage H.chart.symm O hoh hOΓ
  have hYΓ := gamma_subobjectImage G.chart.symm O hog hOΓ
  let ex := gammaSubobjectImageIsoAt H.chart.symm O hoh hOΓ
  let ey := gammaSubobjectImageIsoAt G.chart.symm O hog hOΓ
  let ZH := gammaComplementAt A O hOΓ
  let ZG := gammaComplementAt C O hOΓ
  let DH := @SpecialTransformations.DefinableGeometry.DefSet.sdiff LRV M N _ S H.locus G.locus
  let DG := @SpecialTransformations.DefinableGeometry.DefSet.sdiff LRV M N _ S G.locus H.locus
  let QH := gammaRestrictAt U DH (fun _ h => H.contained h.1) (L.sdiff H.locus_graph G.locus_graph)
  let QG := gammaRestrictAt U DG (fun _ h => G.contained h.1) (L.sdiff G.locus_graph H.locus_graph)
  have hh : (@SpecialTransformations.DefinableGeometry.DefSet.carrier LRV M N _ S (rvObjectDomain ZH.object.obj)) =
      (@SpecialTransformations.DefinableGeometry.DefSet.carrier LRV M N _ S (rvObjectDomain QH.object.obj)) := by
    ext x
    constructor
    · rintro ⟨ha,hn⟩
      exact ⟨ha,fun hb => hn ⟨ha,hb⟩⟩
    · rintro ⟨ha,hn⟩
      exact ⟨ha,fun hab => hn hab.2⟩
  have hg : (@SpecialTransformations.DefinableGeometry.DefSet.carrier LRV M N _ S (rvObjectDomain ZG.object.obj)) =
      (@SpecialTransformations.DefinableGeometry.DefSet.carrier LRV M N _ S (rvObjectDomain QG.object.obj)) := by
    ext x
    constructor
    · rintro ⟨hb,hn⟩
      exact ⟨hb,fun ha => hn ⟨ha,hb⟩⟩
    · rintro ⟨hb,hn⟩
      exact ⟨hb,fun hab => hn hab.1⟩
  let eh' := @rvIsoOfCarrierEq M N S n (rvObjectArity U.object.obj) (rvObjectDomain ZH.object.obj) (rvObjectDomain QH.object.obj)
    (rvObjectVolume ZH.object.obj) (rvObjectVolume QH.object.obj) hh (fun _ => rfl)
  let eg' := @rvIsoOfCarrierEq M N S n (rvObjectArity U.object.obj) (rvObjectDomain ZG.object.obj) (rvObjectDomain QG.object.obj)
    (rvObjectVolume ZG.object.obj) (rvObjectVolume QG.object.obj) hg (fun _ => rfl)
  let Z := @SpecialTransformations.DefinableGeometry.DefSet.univ LRV M N (@rawRVSpace M N (rvObjectArity U.object.obj)) B.real
  let Id := @SpecialTransformations.DefinableGeometry.Map.id LRV M N _ B.real Z
  let exrem := (gammaComplementImageIsoAt H.chart.symm O hoh hOΓ).symm.trans
    (show GammaIsoAt ZH QH from GammaIsoAt.ofAmbientFormula eh' Id (fun _ => rfl))
  let eyrem := (gammaComplementImageIsoAt G.chart.symm O hog hOΓ).symm.trans
    (show GammaIsoAt ZG QG from GammaIsoAt.ofAmbientFormula eg' Id (fun _ => rfl))
  let J := @SpecialTransformations.DefinableGeometry.DefSet.union LRV M N _ S H.locus G.locus
  let J' := @SpecialTransformations.DefinableGeometry.DefSet.union LRV M N _ S G.locus H.locus
  let E := gammaComplementAt U J (L.union H.locus_graph G.locus_graph)
  let E' := gammaComplementAt U J' (L.union G.locus_graph H.locus_graph)
  have he : (@SpecialTransformations.DefinableGeometry.DefSet.carrier LRV M N _ S (rvObjectDomain E'.object.obj)) =
      (@SpecialTransformations.DefinableGeometry.DefSet.carrier LRV M N _ S (rvObjectDomain E.object.obj)) := by
    ext x
    constructor <;> rintro ⟨hu,hn⟩ <;> exact ⟨hu,fun h => hn (h.elim Or.inr Or.inl)⟩
  let eE := @rvIsoOfCarrierEq M N S n (rvObjectArity U.object.obj) (rvObjectDomain E'.object.obj) (rvObjectDomain E.object.obj)
    (rvObjectVolume E'.object.obj) (rvObjectVolume E.object.obj) he (fun _ => rfl)
  let extIso : GammaIsoAt E' E := GammaIsoAt.ofAmbientFormula eE Id (fun _ => rfl)
  exact {
    left := X
    left_subset := hX
    left_graph := hXΓ
    right := Y
    right_subset := hY
    right_graph := hYΓ
    overlap := ex.symm.trans ey
    exterior := E
    left_remainder := (gammaSplitComplementAt U H.locus G.locus G.contained H.locus_graph G.locus_graph).trans
      (gammaCoprodIsoAt eyrem.symm (GammaIsoAt.refl E))
    right_remainder := (gammaSplitComplementAt U G.locus H.locus H.contained G.locus_graph H.locus_graph).trans
      (gammaCoprodIsoAt exrem.symm extIso) }

end IntegrationInACVF.Section6.FiniteRV
