import IntegrationSection6.BlowupPresentations

/-! Definable overlap refinement of two actual blowup loci. -/

open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace IntegrationInACVF.Section6

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {S : Set M} {k : ℕ}

/-- Split the complement of A into B outside A and the common exterior. -/
def splitComplement (U : RVObject (M := M) S k)
    (A B : DefSet (rawRVSpace (M := M) U.arity) S)
    (hB : B.carrier ⊆ U.domain.carrier) :
    U.restrict (complement U A) (complement_subset U A) ≅
      rvCoprodObject (U.restrict (B.sdiff A) (fun _ h => hB h.1))
        (U.restrict (complement U (A.union B)) (complement_subset U (A.union B))) := by
  let R := U.restrict (complement U A) (complement_subset U A)
  let D := B.sdiff A
  have hD : D.carrier ⊆ R.domain.carrier := fun _ h => ⟨hB h.1, h.2⟩
  have he : (complement R D).carrier = (complement U (A.union B)).carrier := by
    ext x
    constructor
    · rintro ⟨⟨hu, hna⟩, hn⟩
      refine ⟨hu, ?_⟩
      rintro (ha | hb)
      · exact hna ha
      · exact hn ⟨hb, hna⟩
    · rintro ⟨hu, hn⟩
      exact ⟨⟨hu, fun ha => hn (Or.inl ha)⟩, fun h => hn (Or.inr h.1)⟩
  exact (partitionIso R D hD).symm.trans (rvCoprodIso
    (rvIsoOfCarrierEq _ _ _ _ rfl (fun _ => rfl))
    (rvIsoOfCarrierEq _ _ _ _ he (fun _ => rfl)))

/-- Two charts over the same original object have a finite definable
four-part refinement. All subobjects stay over the original base. -/
structure OverlapRefinement {U V W : RVObject (M := M) S k}
    (h : Blowup U V) (g : Blowup U W) where
  left : DefSet (rawRVSpace (M := M) h.center.arity) S
  left_subset : left.carrier ⊆ h.center.domain.carrier
  right : DefSet (rawRVSpace (M := M) g.center.arity) S
  right_subset : right.carrier ⊆ g.center.domain.carrier
  overlap : h.center.restrict left left_subset ≅ g.center.restrict right right_subset
  exterior : RVObject (M := M) S k
  left_remainder :
    U.restrict (complement U h.locus) (complement_subset U h.locus) ≅
      rvCoprodObject (g.center.restrict (complement g.center right) (complement_subset _ _)) exterior
  right_remainder :
    U.restrict (complement U g.locus) (complement_subset U g.locus) ≅
      rvCoprodObject (h.center.restrict (complement h.center left) (complement_subset _ _)) exterior

/-- The actual intersection and two differences give the required chart
refinement; no confluence or blowup conclusion is assumed. -/
def overlapRefinement {U V W : RVObject (M := M) S k}
    (h : Blowup U V) (g : Blowup U W) : OverlapRefinement h g := by
  let O := h.locus.inter g.locus
  have hoh : O.carrier ⊆ (U.restrict h.locus h.contained).domain.carrier := fun _ h => h.1
  have hog : O.carrier ⊆ (U.restrict g.locus g.contained).domain.carrier := fun _ h => h.2
  let X := subobjectImage h.chart.symm O hoh
  let Y := subobjectImage g.chart.symm O hog
  have hX := subobjectImage_subset h.chart.symm O hoh
  have hY := subobjectImage_subset g.chart.symm O hog
  let ex := subobjectImageIso h.chart.symm O hoh
  let ey := subobjectImageIso g.chart.symm O hog
  have hxrem :
      (complement (U.restrict h.locus h.contained) O).carrier =
        (h.locus.sdiff g.locus).carrier := by
    ext x
    constructor
    · rintro ⟨ha, hn⟩
      exact ⟨ha, fun hb => hn ⟨ha, hb⟩⟩
    · rintro ⟨ha, hn⟩
      exact ⟨ha, fun hab => hn hab.2⟩
  have hyrem :
      (complement (U.restrict g.locus g.contained) O).carrier =
        (g.locus.sdiff h.locus).carrier := by
    ext x
    constructor
    · rintro ⟨hb, hn⟩
      exact ⟨hb, fun ha => hn ⟨ha, hb⟩⟩
    · rintro ⟨hb, hn⟩
      exact ⟨hb, fun hab => hn hab.1⟩
  let exrem : h.center.restrict (complement h.center X) (complement_subset _ _) ≅
      U.restrict (h.locus.sdiff g.locus) (fun _ hz => h.contained hz.1) :=
    (complementImageIso h.chart.symm O hoh).symm.trans
      (rvIsoOfCarrierEq _ _ _ _ hxrem (fun _ => rfl))
  let eyrem : g.center.restrict (complement g.center Y) (complement_subset _ _) ≅
      U.restrict (g.locus.sdiff h.locus) (fun _ hz => g.contained hz.1) :=
    (complementImageIso g.chart.symm O hog).symm.trans
      (rvIsoOfCarrierEq _ _ _ _ hyrem (fun _ => rfl))
  let E := U.restrict (complement U (h.locus.union g.locus)) (complement_subset _ _)
  have hunion : (g.locus.union h.locus).carrier = (h.locus.union g.locus).carrier :=
    Set.union_comm _ _
  let eExterior : U.restrict (complement U (g.locus.union h.locus)) (complement_subset _ _) ≅ E :=
    rvIsoOfCarrierEq _ _ _ _ (by
      change U.domain.carrier \ (g.locus.union h.locus).carrier =
        U.domain.carrier \ (h.locus.union g.locus).carrier
      rw [hunion]) (fun _ => rfl)
  exact {
    left := X
    left_subset := hX
    right := Y
    right_subset := hY
    overlap := ex.symm.trans ey
    exterior := E
    left_remainder := (splitComplement U h.locus g.locus g.contained).trans
      (rvCoprodIso eyrem.symm (Iso.refl _))
    right_remainder := (splitComplement U g.locus h.locus h.contained).trans
      (rvCoprodIso exrem.symm eExterior) }

end IntegrationInACVF.Section6
