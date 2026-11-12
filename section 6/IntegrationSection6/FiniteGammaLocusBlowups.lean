import IntegrationSection6.FiniteGammaBlowups
import IntegrationSection6.FiniteGammaSubobjects
import IntegrationSection6.FiniteGammaCoproductMaps
import IntegrationSection6.FiniteGammaPartitionCharts
import IntegrationSection6.ComplementTagCoordinates

/-! Gamma split charts yield genuine Gamma-definable loci and complementary
charts, with all objects still in RV[k]. -/
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

structure GammaLocusBlowupAt {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00) (hsmall : Cardinal.mk B.real < κ)
    (U V : GammaObjectAt B S n) where
  center : GammaObjectAt B S n
  coordinate : Fin n
  admissible : GammaAdmissible center.toGamma.toGammaRVObject coordinate
  locus : @SpecialTransformations.DefinableGeometry.DefSet LRV M N (@rawRVSpace M N (rvObjectArity U.object.obj)) S
  contained : (@SpecialTransformations.DefinableGeometry.DefSet.carrier LRV M N _ S locus) ⊆
    (@SpecialTransformations.DefinableGeometry.DefSet.carrier LRV M N _ S (rvObjectDomain U.object.obj))
  locus_graph : GammaSetDefinable B {p : Point (M := M) 0 (rvObjectArity U.object.obj) |
    p.2 ∈ @SpecialTransformations.DefinableGeometry.DefSet.carrier LRV M N _ S locus}
  chart : GammaIsoAt center (gammaRestrictAt U locus contained locus_graph)
  result : GammaIsoAt V (gammaCoprodAt
    (gammaElementaryAt hκ hs h00 hsmall  center coordinate admissible) (gammaComplementAt U locus locus_graph))

variable {κ : Cardinal} {hκ : Cardinal.aleph0 ≤ κ} {hs : Saturated M κ}

variable {h00 : M ⊨ Axioms.ACVF00} {hsmall : Cardinal.mk B.real < κ}

variable {U V : GammaObjectAt B S n}

def gammaLeftLocus (C R : GammaObjectAt B S n) :=
  @SpecialTransformations.DefinableGeometry.Map.image LRV M N _ _ S _ _
    (@rvLeftTagMap M N hN S (rvObjectArity C.object.obj) (rvObjectDomain C.object.obj) (rvObjectArity R.object.obj))

def gammaLeftRestrictionIsoAt (C R : GammaObjectAt B S n) :
    GammaIsoAt C (gammaRestrictAt (gammaCoprodAt C R)
      (gammaLeftLocus C R)
      (fun _ h => Or.inl h) (gamma_rv_map_image (@rvLeftTagMap M N hN S (rvObjectArity C.object.obj) (rvObjectDomain C.object.obj) (rvObjectArity R.object.obj)) (gamma_leftTag_graph C (rvObjectArity R.object.obj)))) := by
  apply GammaIsoAt.ofAmbient (@rvCoprodLeftRestrictionIso M N hN S n C.object.obj R.object.obj)
  exact gamma_leftTag_graph C (rvObjectArity R.object.obj)

def gammaCoprodComplementIsoAt (C R : GammaObjectAt B S n) :
    GammaIsoAt R (gammaComplementAt (gammaCoprodAt C R)
      (gammaLeftLocus C R)
      (gamma_rv_map_image (@rvLeftTagMap M N hN S (rvObjectArity C.object.obj) (rvObjectDomain C.object.obj) (rvObjectArity R.object.obj)) (gamma_leftTag_graph C (rvObjectArity R.object.obj)))) := by
  apply GammaIsoAt.ofAmbient (@coprodComplementIso M N hN S n C.object.obj R.object.obj).symm
  apply GammaGraphDefinable.congr (gamma_rightTag_graph R (rvObjectArity C.object.obj))
  intro p q
  apply exists_congr
  intro u
  rw [@coprodComplementIso_symm_labels M N hN S n C.object.obj R.object.obj u]

def GammaBlowupAt.toLocus (H : GammaBlowupAt hκ hs h00 hsmall  U V) :
    GammaLocusBlowupAt hκ hs h00 hsmall  U V := by
  let C := H.center
  let R := H.remainder
  let W := gammaCoprodAt C R
  let A := (gammaLeftLocus C R)
  have hA : (@SpecialTransformations.DefinableGeometry.DefSet.carrier LRV M N _ S A) ⊆
      (@SpecialTransformations.DefinableGeometry.DefSet.carrier LRV M N _ S (rvObjectDomain W.object.obj)) := fun _ h => Or.inl h
  have hΓ := gamma_rv_map_image (@rvLeftTagMap M N hN S (rvObjectArity C.object.obj) (rvObjectDomain C.object.obj) (rvObjectArity R.object.obj)) (gamma_leftTag_graph C (rvObjectArity R.object.obj))
  let E := isoAtAmbient H.source.symm.iso
  let L := @subobjectImage M N S n W.object.obj U.object.obj E A hA
  have hL := gamma_subobjectImage H.source.symm A hA hΓ
  have hc := @subobjectImage_subset M N hN S n W.object.obj U.object.obj E A hA
  let eC := (gammaLeftRestrictionIsoAt C R).trans (gammaSubobjectImageIsoAt H.source.symm A hA hΓ)
  let eR := (gammaCoprodComplementIsoAt C R).trans (gammaComplementImageIsoAt H.source.symm A hA hΓ)
  exact {
    center := C
    coordinate := H.coordinate
    admissible := H.admissible
    locus := L
    contained := hc
    locus_graph := hL
    chart := eC
    result := H.result.trans (gammaCoprodIsoAt (GammaIsoAt.refl _) eR) }

def GammaLocusBlowupAt.toSplit (H : GammaLocusBlowupAt hκ hs h00 hsmall  U V) :
    GammaBlowupAt hκ hs h00 hsmall  U V where
  center := H.center
  remainder := gammaComplementAt U H.locus H.locus_graph
  coordinate := H.coordinate
  admissible := H.admissible
  source := (gammaPartitionIsoAt U H.locus H.contained H.locus_graph).symm.trans
    (gammaCoprodIsoAt H.chart.symm (GammaIsoAt.refl _))
  result := H.result

end IntegrationInACVF.Section6.FiniteRV
