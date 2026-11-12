import IntegrationSection6.LiftLoci

/-! Old-label images of an RV-pullback partition of a literal lift form
a genuine disjoint definable partition of its input RV domain. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section4 SpecialTransformations.Section5
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {S : Set M} {n : ℕ}
local notation "N" => (@CanonicalStructure.normalize M sM)
local notation "hN" => (@CanonicalStructure.normalized_model M sM hM)

theorem normalizedPresentsLift_labels_sameRV {U : @RVObject M N S n}
    {A : SpecialTransformations.Section5.DefSet (M := M) S n (rvObjectArity U)}
    (h : @PresentsLift M N hN S n U (normalizedPointSet A))
    (a b : A) (hab : a.val.2 = b.val.2) : SameRV a.val b.val := by
  obtain ⟨u,hu,hv⟩ := (h a.val).mp a.property
  obtain ⟨v,hvlabels,hvv⟩ := (h b.val).mp b.property
  have he : u = v := Subtype.ext (hu.trans (hab.trans hvlabels.symm))
  apply (sameRV_iff _ _).mpr
  refine ⟨?_,hab⟩
  intro j
  have hr : @rv M N hN (a.val.1 j) = @rv M N hN (b.val.1 j) :=
    (congrFun hv j).symm.trans ((congrArg (fun w => @RVObject.value M N S n U w j) he).trans (congrFun hvv j))
  exact (rv_normalize _).symm.trans (hr.trans (rv_normalize _))

theorem liftLabelLoci_disjoint {U : @RVObject M N S n}
    {A C E : SpecialTransformations.Section5.DefSet (M := M) S n (rvObjectArity U)}
    (h : @PresentsLift M N hN S n U (normalizedPointSet A))
    (hCA : carrier C ⊆ carrier A) (hEA : carrier E ⊆ carrier A)
    (hCE : Disjoint (carrier C) (carrier E)) (hC : IsRVPullback (carrier C)) :
    Disjoint (carrier (liftLabelLocus C)) (carrier (liftLabelLocus E)) := by
  apply Set.disjoint_left.mpr
  rintro r ⟨c,hc⟩ ⟨e,he⟩
  have hs := normalizedPresentsLift_labels_sameRV h
    ⟨c.val,hCA c.property⟩ ⟨e.val,hEA e.property⟩ (hc.trans he.symm)
  exact Set.disjoint_left.mp hCE ((isRVPullback_iff _).mp hC c.val c.property e.val hs) e.property

theorem liftLabelLoci_cover {U : @RVObject M N S n}
    {A C E : SpecialTransformations.Section5.DefSet (M := M) S n (rvObjectArity U)}
    (h : @PresentsLift M N hN S n U (normalizedPointSet A))
    (hA : carrier A = carrier C ∪ carrier E) :
    carrier (rvObjectDomain U) = carrier (liftLabelLocus C) ∪ carrier (liftLabelLocus E) := by
  ext r
  constructor
  · intro hr
    obtain ⟨p,hp,_⟩ := @PresentsLift.representative M N hN S n U (normalizedPointSet A) h ⟨r,hr⟩
    have hm := (Set.ext_iff.mp hA p.val).mp p.property
    rcases hm with hc | he
    · exact Or.inl ⟨⟨p.val,hc⟩,hp⟩
    · exact Or.inr ⟨⟨p.val,he⟩,hp⟩
  · rintro (hr | hr)
    · exact liftLabelLocus_subset h (fun p hp => (Set.ext_iff.mp hA p).mpr (Or.inl hp)) hr
    · exact liftLabelLocus_subset h (fun p hp => (Set.ext_iff.mp hA p).mpr (Or.inr hp)) hr

end IntegrationInACVF.Section6
