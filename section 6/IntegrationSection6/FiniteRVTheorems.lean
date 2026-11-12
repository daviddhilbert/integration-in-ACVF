import IntegrationSection6.FiniteRVGeometry

/-! Numbered blowup and congruence statements for RV[k] only. All output
objects, common refinements and isomorphisms belong to the finite category. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
namespace IntegrationInACVF.Section6.FiniteRV
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {S : Set M} {k : ℕ}

theorem lemma_6_3 {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (hsmall : Cardinal.mk S < κ)
    {U V U' V' : RVFiniteObject (M := M) S k}
    (hU : ElementaryBlowup U U') (hV : ElementaryBlowup V V') (e : U ≅ V) :
    Nonempty (U' ≅ V') :=
  (IntegrationInACVF.Section6.lemma_6_3 hκ hs hsmall hU hV
    ((finiteVolumeProperty S k).ι.mapIso e)).map rvFiniteIsoOfAmbient

theorem lemma_6_5 {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (hsmall : Cardinal.mk S < κ)
    {U V A B : RVFiniteObject (M := M) S k} {r s : ℕ}
    (e : U ≅ V) (h : IteratedBlowup r U A) (g : IteratedBlowup s V B) :
    ∃ A' B' : RVFiniteObject (M := M) S k,
      IteratedBlowup s A A' ∧ IteratedBlowup r B B' ∧ Nonempty (A' ≅ B') := by
  obtain ⟨A',B',ha,hb,he⟩ := IntegrationInACVF.Section6.lemma_6_5 hκ hs hsmall
    ((finiteVolumeProperty S k).ι.mapIso e) h.toAmbient g.toAmbient
  have hA' := ha.finite_volume hκ hs hsmall A.property
  have hB' := hb.finite_volume hκ hs hsmall B.property
  exact ⟨⟨A',hA'⟩,⟨B',hB'⟩,
    ambientChain_toFinite hκ hs hsmall ha A.property hA',
    ambientChain_toFinite hκ hs hsmall hb B.property hB',he.map rvFiniteIsoOfAmbient⟩

theorem corollary_6_6 {U V U' V' : RVFiniteObject (M := M) S k}
    (h : Isp U V) (e : U' ≅ U) (f : V' ≅ V) : Isp U' V' := by
  obtain ⟨r,s,A,B,hu,hv,he⟩ := h
  have changeSource {r : ℕ} {X Y Z : RVFiniteObject (M := M) S k}
      (t : IteratedBlowup r X Y) (g : Z ≅ X) : IteratedBlowup r Z Y := by
    cases t with
    | zero h => exact .zero (h.map g.trans)
    | cons h ht => exact .cons (h.sourceIso ((finiteVolumeProperty S k).ι.mapIso g)) ht
  exact ⟨r,s,A,B,changeSource hu e,changeSource hv f,he⟩

theorem isp_equivalence {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (hsmall : Cardinal.mk S < κ) :
    Equivalence (Isp (M := M) (S := S) (k := k)) := by
  constructor
  · intro U
    exact ⟨0,0,U,U,.zero ⟨Iso.refl U⟩,.zero ⟨Iso.refl U⟩,⟨Iso.refl U⟩⟩
  · rintro U V ⟨r,s,A,B,hu,hv,he⟩
    exact ⟨s,r,B,A,hv,hu,he.map Iso.symm⟩
  · intro U V W huv hvw
    apply (isp_iff_finiteIsp hκ hs hsmall U W).mpr
    exact IntegrationInACVF.Section6.Isp.trans hκ hs hsmall
      ((isp_iff_finiteIsp hκ hs hsmall U V).mp huv)
      ((isp_iff_finiteIsp hκ hs hsmall V W).mp hvw)

theorem lemma_6_8_add_class_iff {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (hsmall : Cardinal.mk S < κ)
    (U V : RVFiniteObject (M := M) S k) :
    finiteIspAddCon hκ hs hsmall (rvFiniteClass U) (rvFiniteClass V) ↔ Isp U V :=
  (finiteIspAddCon_class_iff hκ hs hsmall U V).trans (isp_iff_finiteIsp hκ hs hsmall U V).symm

theorem lemma_6_8_mul_class_iff {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (hsmall : Cardinal.mk S < κ)
    (U V : RVFiniteObject (M := M) S k) :
    finiteIspRingCon hκ hs hsmall (rvFiniteGradedClass U) (rvFiniteGradedClass V) ↔ Isp U V :=
  (finiteIspRingCon_class_iff hκ hs hsmall U V).trans (isp_iff_finiteIsp hκ hs hsmall U V).symm

end IntegrationInACVF.Section6.FiniteRV
