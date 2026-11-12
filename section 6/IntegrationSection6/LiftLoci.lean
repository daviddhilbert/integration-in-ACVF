import IntegrationSection6.NormalizedFocus
import IntegrationSection6.LiftCarrierGeometry
import Section4.MapCorestrict

/-! An RV-pullback sublocus of a literal lift is exactly the lift of its
old-label image. The parameter base and actual raw RV presentation are retained. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
  SpecialTransformations.Section4.rawVFSpace SpecialTransformations.Section4.rawRVSpace
  SpecialTransformations.Section4.rawMixedSpace SpecialTransformations.DefinableGeometry.Space.ofEmbedding
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section4 SpecialTransformations.Section5
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {S : Set M} {n m : ℕ}
local notation "N" => (@CanonicalStructure.normalize M sM)
local notation "hN" => (@CanonicalStructure.normalized_model M sM hM)

def pointRVLabelsMap (A : SpecialTransformations.Section5.DefSet (M := M) S n m) :
    Map A (PresentedSet.univ (SpecialTransformations.Section5.rawRVSpace m) S) :=
  Map.comp (@SpecialTransformations.DefinableGeometry.Map.snd LRV M N
    (@SpecialTransformations.Section4.rawVFSpace M N n)
    (@SpecialTransformations.Section4.rawRVSpace M N m) S
    (PresentedSet.univ (rawPointSpace n m) S)) (rawPointMap A)

@[simp] theorem pointRVLabelsMap_value (A : SpecialTransformations.Section5.DefSet (M := M) S n m)
    (a : A) : (pointRVLabelsMap A a).val = a.val.2 := rfl

def liftLabelLocus (C : SpecialTransformations.Section5.DefSet (M := M) S n m) :=
  Map.image (pointRVLabelsMap C)

theorem liftLabelLocus_mem (C : SpecialTransformations.Section5.DefSet (M := M) S n m)
    (t : Fin m → CanonicalRV.RVSort M) :
    t ∈ carrier (liftLabelLocus C) ↔ ∃ p : C, p.val.2 = t := Iff.rfl

theorem liftLabelLocus_subset {U : @RVObject M N S n}
    {A C : SpecialTransformations.Section5.DefSet (M := M) S n (rvObjectArity U)}
    (h : @PresentsLift M N hN S n U (normalizedPointSet A))
    (hCA : carrier C ⊆ carrier A) :
    carrier (liftLabelLocus C) ⊆ carrier (rvObjectDomain U) := by
  rintro t ⟨a,ha⟩
  obtain ⟨u,hu,_⟩ := (h a.val).mp (hCA a.property)
  change a.val.2 = t at ha
  exact (hu.trans ha) ▸ u.property

theorem normalizedPresentsLift_sublocus {U : @RVObject M N S n}
    {A C : SpecialTransformations.Section5.DefSet (M := M) S n (rvObjectArity U)}
    (h : @PresentsLift M N hN S n U (normalizedPointSet A))
    (hCA : carrier C ⊆ carrier A) (hC : IsRVPullback (carrier C)) :
    @PresentsLift M N hN S n
      (@RVObject.restrict M N S n U (liftLabelLocus C) (liftLabelLocus_subset h hCA))
      (normalizedPointSet C) := by
  have hCN := (pullback_normalize (carrier C)).mpr hC
  let L := liftLabelLocus C
  have hc := liftLabelLocus_subset h hCA
  letI := N
  letI := hN
  intro p
  constructor
  · intro hp
    obtain ⟨u,hu,hv⟩ := (h p).mp (hCA hp)
    let v : L := ⟨u.val,⟨⟨p,hp⟩,hu.symm⟩⟩
    refine ⟨v,hu,?_⟩
    exact hv
  · rintro ⟨u,hu,hv⟩
    obtain ⟨a,ha⟩ := u.property
    change a.val.2 = u.val at ha
    obtain ⟨v,hva,hvv⟩ := (h a.val).mp (hCA a.property)
    have hev : v = (⟨u.val,hc u.property⟩ : U.domain) := Subtype.ext (hva.trans ha)
    have hrv : (fun j => @rv M N hN (a.val.1 j)) = fun j => @rv M N hN (p.1 j) := by
      rw [← hvv,hev]
      exact hv
    exact (isRVPullback_iff _).mp hCN a.val a.property p
      ((sameRV_iff _ _).mpr ⟨fun j => congrFun hrv j,ha.trans hu⟩)

end IntegrationInACVF.Section6
