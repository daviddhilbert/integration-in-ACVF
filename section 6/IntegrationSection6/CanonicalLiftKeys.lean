import IntegrationSection6.CanonicalRVKeys
import IntegrationSection6.NormalizedFocus
import IntegrationSection6.LiftCarrierGeometry

/-! Preparatory canonical labeling gives the tag needed for a focus.
The literal lift interface follows from the existing lift equations, with
no added parameter and no cardinal bound on the presentation code set. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section4 SpecialTransformations.Section5
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {S : Set M} {n m : ℕ}

theorem PresentsLift.canonical {U : RVObject (M := M) S n}
    {A : SpecialTransformations.Section5.DefSet (M := M) S n U.arity}
    (h : PresentsLift U A) :
    PresentsLift (canonicalRVKeyObject U) (canonicalImage A) := by
  intro p
  constructor
  · intro hp
    obtain ⟨a,ha,rfl⟩ := (Set.ext_iff.mp (canonicalImage_carrier A) p).mp hp
    obtain ⟨u,hu,hv⟩ := (h a).mp ha
    let v := (canonicalRVKeyIso U).hom.map u
    refine ⟨v,?_,?_⟩
    · change rvAppend (U.value u) u.val = (SpecialTransformations.Section5.canonical a).2
      rw [hv,hu]
      rfl
    · exact (canonicalRVKeyIso_volume U u).trans hv
  · rintro ⟨v,hlabels,hvol⟩
    obtain ⟨u,hu⟩ := v.property
    have he : v = (canonicalRVKeyIso U).hom.map u := Subtype.ext hu.symm
    rw [he,canonicalRVKeyIso_volume] at hvol
    have ht : rvAppend (U.value u) u.val = p.2 := hu.trans hlabels
    let a : Point (M := M) n U.arity := (p.1,u.val)
    have ha : a ∈ carrier A := (h a).mpr ⟨u,rfl,hvol⟩
    apply (Set.ext_iff.mp (canonicalImage_carrier A) p).mpr
    refine ⟨a,ha,?_⟩
    apply Prod.ext
    · rfl
    · change rvAppend (fun j => rv (p.1 j)) u.val = p.2
      exact (congrArg (fun r => rvAppend r u.val) hvol.symm).trans ht

theorem canonicalLiftKeys_tagged (A : SpecialTransformations.Section5.DefSet (M := M) S n m)
    (i : Fin n) : Tagged (carrier (canonicalImage A)) i (Fin.castAdd m i) := by
  rw [canonicalImage_carrier]
  exact canonical_tagged (carrier A) i

local notation "N" => (@CanonicalStructure.normalize M sM)
local notation "hN" => (@CanonicalStructure.normalized_model M sM hM)

theorem canonicalPoint_normalize (p : Point (M := M) n m) :
    @canonical M N hN n m p = canonical p := by
  apply Prod.ext
  · rfl
  · exact congrArg (fun q : Key (M := M) n m => Fin.append q.1 q.2)
      (@key_normalize M sM hM n m p)

theorem canonicalImage_normalize (A : SpecialTransformations.Section5.DefSet (M := M) S n m) :
    @canonicalImage M N hN n m S (normalizedPointSet A) =
      @normalizedPointSet M sM hM S n (n+m) (canonicalImage A) := by
  apply @SpecialTransformations.DefinableGeometry.DefSet.eq_of_carrier_eq LRV M
    (@CanonicalStructure.normalize M N) (@pointSpace M N hN n (n+m)) S _ _
  ext p
  constructor
  · rintro ⟨a,ha⟩
    refine ⟨⟨a.val,a.property⟩,?_⟩
    change @canonical M sM hM n m a.val = p
    change @canonical M N hN n m a.val = p at ha
    exact (@canonicalPoint_normalize M sM hM n m a.val).symm.trans ha
  · rintro ⟨a,ha⟩
    refine ⟨⟨a.val,a.property⟩,?_⟩
    change @canonical M N hN n m a.val = p
    change @canonical M sM hM n m a.val = p at ha
    exact (@canonicalPoint_normalize M sM hM n m a.val).trans ha

end IntegrationInACVF.Section6
