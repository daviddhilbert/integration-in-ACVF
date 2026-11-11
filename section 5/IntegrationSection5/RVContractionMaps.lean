import IntegrationSection5.QuotientBijection
import Section5.PullbackLift

/-! Definable contraction maps between the actual RV objects of pullbacks, with quotient bijectivity and volume projection formulas. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5

namespace IntegrationInACVF.Section5
variable {M : Type} [sM : LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {S : Set M} {n m l : ℕ}
variable {A : DefSet (M := M) S n m} {B : DefSet (M := M) S n l}

theorem rawKeyMap_eq_iff (a b : A) :
    (rawKeyMap A a).val = (rawKeyMap A b).val ↔ SameRV a.val b.val := by
  rw [rawKeyMap_apply,rawKeyMap_apply]
  constructor
  · intro he
    apply (sameRV_iff _ _).mpr
    constructor
    · intro i
      simpa only [Fin.append_left,vfAt] using congrFun he (Fin.castAdd m i)
    · funext i
      simpa only [Fin.append_right] using congrFun he (Fin.natAdd n i)
  · intro he
    exact congrArg (fun p : Key (M := M) n m => Fin.append p.1 p.2) he

def rvContractionMap (f : Map A B) (hc : Contractible f) :
    Map (rvObjectDomain (pullbackObject A)) (rvObjectDomain (pullbackObject B)) :=
  Map.descend (rawKeyMap A) (Map.comp (Map.toImage (rawKeyMap B)) f) (by
    intro a b he
    apply Subtype.ext
    exact (rawKeyMap_eq_iff (f a) (f b)).mpr (hc a b ((rawKeyMap_eq_iff a b).mp he)))

theorem rvContractionMap_spec (f : Map A B) (hc : Contractible f) (a : A) :
    rvContractionMap f hc (Map.toImage (rawKeyMap A) a) = Map.toImage (rawKeyMap B) (f a) :=
  Map.descend_apply _ _ _ a

theorem rawKeyImage_surjective (A : DefSet (M := M) S n m) :
    Function.Surjective (Map.toImage (rawKeyMap A)) := by
  intro u
  exact ⟨Map.imageRepresentative (rawKeyMap A) u,Subtype.ext (Map.imageRepresentative_spec _ u)⟩

theorem rvContractionMap_bijective (f : Map A B) (hf : Function.Bijective f)
    (hc : Contractible f) (hback : Contractible (Map.inverse f hf)) :
    Function.Bijective (rvContractionMap f hc) := by
  constructor
  · intro x y he
    obtain ⟨a,rfl⟩ := rawKeyImage_surjective A x
    obtain ⟨b,rfl⟩ := rawKeyImage_surjective A y
    rw [rvContractionMap_spec,rvContractionMap_spec] at he
    have hval := congrArg (fun z : rvObjectDomain (pullbackObject B) => z.val) he
    have hRV : SameRV (f a).val (f b).val :=
      (rawKeyMap_eq_iff (f a) (f b)).mp hval
    have hInv := hback (f a) (f b) hRV
    rw [Map.inverse_apply,Map.inverse_apply] at hInv
    exact Subtype.ext ((rawKeyMap_eq_iff a b).mpr hInv)
  · intro y
    obtain ⟨b,rfl⟩ := rawKeyImage_surjective B y
    obtain ⟨a,rfl⟩ := hf.2 b
    exact ⟨Map.toImage (rawKeyMap A) a,rvContractionMap_spec f hc a⟩

theorem pullbackObject_value_key (a : A) :
    (rvObjectVolume (pullbackObject A) (Map.toImage (rawKeyMap A) a)).val = fun i => rv (vfAt a.val i) := by
  funext i
  change (rawKeyMap A a).val (Fin.castAdd m i) = rv (vfAt a.val i)
  rw [rawKeyMap_apply,Fin.append_left]

theorem rvContractionMap_volume_spec (f : Map A B) (hc : Contractible f) (a : A) :
    (rvObjectVolume (pullbackObject B) (rvContractionMap f hc (Map.toImage (rawKeyMap A) a))).val =
      fun i => rv (vfAt (f a).val i) := by
  rw [rvContractionMap_spec,pullbackObject_value_key]

end IntegrationInACVF.Section5
