import IntegrationSection3ACVF.BallPresentation

/-!
# Ball cosets inside a complete type

The ball family is the range of the actual first-order coset relation of a
definable additive subgroup of VF. Its interpreted equality is tested on all
real codes. No centre is added to the parameter base.
-/

set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3
open IntegrationInACVF.Section3 IntegrationInACVF.Section3.ImaginaryFamilies

namespace IntegrationInACVF.Section3ACVF.BallCosetAtomicity

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

def cosetBody (H : AddSubgroup (VFType (M := M))) (a : VFType (M := M)) : Set M :=
  Subtype.val '' {x | QuotientAddGroup.mk' H x = QuotientAddGroup.mk' H a}

/-- The first coordinate is the centre and the second is the point. -/
def cosetRelation (H : AddSubgroup (VFType (M := M))) : Set (M × M) :=
  {p | ![p.2,p.1] ∈ DefinableCosets.relation (Subtype.val '' (H : Set (VFType (M := M))))}

theorem cosetRelation_definable (Q : Set M) (H : AddSubgroup (VFType (M := M)))
    (hH : DefinableAt Q .vf (Subtype.val '' (H : Set (VFType (M := M))))) :
    @Set.Definable₂ M Q LRV (CanonicalStructure.normalize (M := M)) (cosetRelation H) := by
  have hs := DefinableCosets.relation_definable Q _ hH
  have hr := ((@definableOver_iff_normalized_raw M sM hM Q 2 (fun _ => .vf) _).mp hs).1
  let R := cosetRelation H
  letI := CanonicalStructure.normalize (M := M)
  change Q.Definable LRV {z : Fin 2 → M | (z 0,z 1) ∈ R}
  convert hr.preimage_comp (![1,0] : Fin 2 → Fin 2) using 1
  ext z
  rfl

theorem cosetRelation_fibre (H : AddSubgroup (VFType (M := M))) (a : VFType (M := M)) :
    DefinableFamilies.fibre (cosetRelation H) a.val = cosetBody H a := by
  ext x
  constructor
  · intro hx
    have hxf : iVF x := hx.1
    let u : VFType (M := M) := ⟨x,hxf⟩
    exact ⟨u,(DefinableCosets.mem_relation H u a).mp hx,rfl⟩
  · rintro ⟨u,hu,rfl⟩
    exact (DefinableCosets.mem_relation H u a).mpr hu

def cosetFamily (H : AddSubgroup (VFType (M := M))) : Set (BallImaginaries.Ball M) :=
  rangeFamily BallImaginaries.underlying {x | iVF x} (cosetRelation H)

theorem cosetFamily_definable (Q : Set M) (H : AddSubgroup (VFType (M := M)))
    (hH : DefinableAt Q .vf (Subtype.val '' (H : Set (VFType (M := M))))) :
    @Presentation.DefinableFamily LRV M (CanonicalStructure.normalize (M := M))
      (BallImaginaries.Ball M) (Fin 4) BallPresentation.presentation Q (cosetFamily H) := by
  have hp := BallPresentation.presentation_definable (M := M) Q
  have hm := BallPresentation.membership_definable (M := M) Q
  have hr := cosetRelation_definable Q H hH
  have hd := ((@definableAt_iff_normalized_raw M sM hM Q .vf _).mp
    (@definableAt_sort M sM Q .vf)).1
  letI := CanonicalStructure.normalize (M := M)
  exact rangeFamily_definable hp hm hd hr

theorem cosetFamily_disjoint (H : AddSubgroup (VFType (M := M))) :
    (cosetFamily H).Pairwise fun i j =>
      Disjoint (BallImaginaries.underlying i) (BallImaginaries.underlying j) := by
  intro i hi j hj hne
  apply Set.disjoint_left.mpr
  intro x hxi hxj
  obtain ⟨a,ha,hia⟩ := hi
  obtain ⟨b,hb,hjb⟩ := hj
  let a' : VFType (M := M) := ⟨a,ha⟩
  let b' : VFType (M := M) := ⟨b,hb⟩
  have hiB : BallImaginaries.underlying i = cosetBody H a' :=
    hia.trans (cosetRelation_fibre H a')
  have hjB : BallImaginaries.underlying j = cosetBody H b' :=
    hjb.trans (cosetRelation_fibre H b')
  rw [hiB] at hxi
  rw [hjB] at hxj
  obtain ⟨u,hu,hux⟩ := hxi
  obtain ⟨v,hv,hvx⟩ := hxj
  have huv : u = v := Subtype.ext (hux.trans hvx.symm)
  have hab : QuotientAddGroup.mk' H a' = QuotientAddGroup.mk' H b' :=
    hu.symm.trans ((congrArg (QuotientAddGroup.mk' H) huv).trans hv)
  apply hne
  apply BallImaginaries.underlying_injective
  rw [hiB,hjB]
  unfold cosetBody
  rw [hab]

/-- The coset-family instance of the argument for Lemma 3.4. The ambient
complete-type-generating set is not assumed definable. `H` is an actual
definable additive subgroup, rather than an atomicity or ball-choice input. -/
theorem atomic_ball_coset_below_complete_type (Q : Set M)
    (H : AddSubgroup (VFType (M := M)))
    (hH : DefinableAt Q .vf (Subtype.val '' (H : Set (VFType (M := M)))))
    {A : Set M}
    (hA : @GeneratesCompleteType LRV M (CanonicalStructure.normalize (M := M)) (Fin 1) Q
      {z | z 0 ∈ A})
    (i : BallImaginaries.Ball M) (ha : ∃ a : VFType (M := M),
      BallImaginaries.underlying i = cosetBody H a)
    (hsub : BallImaginaries.underlying i ⊆ A) :
    @Presentation.AtomicWith LRV M (CanonicalStructure.normalize (M := M))
      (BallImaginaries.Ball M) (Fin 4) BallPresentation.presentation Q i
      (BallImaginaries.underlying i) := by
  let T := cosetFamily H
  let C : BallImaginaries.Ball M → Set M :=
    fun j => {x | j ∈ T ∧ x ∈ BallImaginaries.underlying j}
  have hi : i ∈ T := by
    obtain ⟨a,ha⟩ := ha
    exact ⟨a.val,a.property,ha.trans (cosetRelation_fibre H a).symm⟩
  have hp := BallPresentation.presentation_definable (M := M) Q
  have ht := cosetFamily_definable Q H hH
  have hm := BallPresentation.membership_definable (M := M) Q
  have hc : @Presentation.DefinableRelation LRV M (CanonicalStructure.normalize (M := M))
      (BallImaginaries.Ball M) (Fin 4) BallPresentation.presentation Q C := by
    letI := CanonicalStructure.normalize (M := M)
    exact hm.restrict ht
  have hd := cosetFamily_disjoint H
  have hdis : T.Pairwise fun j k => Disjoint (C j) (C k) := by
    intro j hj k hk hne
    exact Set.disjoint_left.mpr fun x hxj hxk =>
      Set.disjoint_left.mp (hd hj hk hne) hxj.2 hxk.2
  have hCi : C i = BallImaginaries.underlying i := by
    ext x
    exact and_iff_right hi
  have hCA : C i ⊆ A := fun x hx => hsub hx.2
  let p := BallPresentation.presentation (M := M)
  letI := CanonicalStructure.normalize (M := M)
  have h := atomic_below_complete_type hp ht hc hdis hA hi hCA
  change p.AtomicWith (L := LRV) Q i (C i) at h
  rw [hCi] at h
  exact h

end IntegrationInACVF.Section3ACVF.BallCosetAtomicity
