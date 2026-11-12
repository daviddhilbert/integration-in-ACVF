import IntegrationSection6.ProductGeometry
import IntegrationSection6.ElementaryKeys

/-! Elementary blowup in the second factor, using the checked cartesian
associator on the actual three label blocks. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {S : Set M} {k l : ℕ}

def positiveParameterObject (S : Set M) : RVObject (M := M) S 0 :=
  RVObject.mk 1 (positiveRV S) (selectRVTuple (Fin.elim0 : Fin 0 → Fin 1) (positiveRV S))

theorem blowupValue_append_right (i : Fin k) (u : Fin k → CanonicalRV.RVSort M)
    (r : Fin l → CanonicalRV.RVSort M) (s : CanonicalRV.RVSort M) :
    blowupValue (Fin.natAdd l i) (rvAppend r u) s = rvAppend r (blowupValue i u s) := by
  funext a
  refine Fin.addCases (fun j => ?_) (fun j => ?_) a
  · have hn : Fin.castAdd k j ≠ Fin.natAdd l i := by
      intro h
      have he := congrArg Fin.val h
      change j.val = l+i.val at he
      omega
    simp only [blowupValue,hn,ite_false,rvAppend,Fin.append_left]
  · have he : (Fin.natAdd l j = Fin.natAdd l i) ↔ j = i := by
      constructor
      · intro h
        apply Fin.ext
        have hv := congrArg Fin.val h
        change l+j.val = l+i.val at hv
        omega
      · exact congrArg (Fin.natAdd l)
    simp only [blowupValue,rvAppend,Fin.append_right,he]

def elementaryRightProductMap (R : RVObject (M := M) S l) (U : RVObject (M := M) S k) (i : Fin k) :
    Map (elementary (rvProductObject R U) (Fin.natAdd l i)).domain (rvProductObject R (elementary U i)).domain :=
  rvProductAssocMap R U (positiveParameterObject S)

theorem elementaryRightProductMap_bijective (R : RVObject (M := M) S l) (U : RVObject (M := M) S k) (i : Fin k) :
    Function.Bijective (elementaryRightProductMap R U i) :=
  rvProductAssocMap_bijective R U (positiveParameterObject S)

theorem elementaryRightProductMap_pair (R : RVObject (M := M) S l) (U : RVObject (M := M) S k) (i : Fin k)
    (r : R.domain) (u : U.domain) (s : positiveRV (M := M) S) :
    elementaryRightProductMap R U i
      (rvPackPair (rvProductObject R U).domain (positiveRV S) (rvPackPair R.domain U.domain r u) s) =
      rvPackPair R.domain (elementary U i).domain r (rvPackPair U.domain (positiveRV S) u s) :=
  rvProductAssocMap_pair R U (positiveParameterObject S) r u s

def elementaryRightProductIso (R : RVObject (M := M) S l) (U : RVObject (M := M) S k) (i : Fin k) :
    elementary (rvProductObject R U) (Fin.natAdd l i) ≅ rvProductObject R (elementary U i) := by
  apply rvIsoOfVolumePreservingBijection (elementaryRightProductMap R U i) (elementaryRightProductMap_bijective R U i)
  intro p
  obtain ⟨ru,s,rfl⟩ := exists_rvPackPair (rvProductObject R U).domain (positiveRV S) p
  obtain ⟨r,u,rfl⟩ := exists_rvPackPair R.domain U.domain ru
  rw [elementaryRightProductMap_pair,rvProductObject_value_pair,elementary_value,
    elementaryProjection_pair,elementaryParameter_pair,elementary_value,
    elementaryProjection_pair,elementaryParameter_pair,rvProductObject_value_pair]
  exact (blowupValue_append_right i (U.value u) (R.value r) (s.val 0)).symm

end IntegrationInACVF.Section6
