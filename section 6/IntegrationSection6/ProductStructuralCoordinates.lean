import Section4.RVProductAssociativity
import Section4.RVProductUnits

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] {S : Set M} {k l j : ℕ}

theorem rvProductSwapMap_labels (U : RVObject (M := M) S k) (V : RVObject (M := M) S l)
    (x : (rvProductObject U V).domain) :
    (rvProductSwapMap U V x).val = fun i => x.val ((finAddFlip : Fin (U.arity+V.arity) ≃ Fin (V.arity+U.arity)).symm i) := by
  obtain ⟨u,v,rfl⟩ := exists_rvPackPair U.domain V.domain x
  have hp : rvProductSwapMap U V (rvPackPair U.domain V.domain u v) = rvPackPair V.domain U.domain v u := by
    simp only [rvProductSwapMap,rvPackPair,Map.comp_apply,rvUnpack_pack]
    rfl
  rw [hp]
  change rvAppend v.val u.val = fun i => rvAppend u.val v.val (finAddFlip.symm i)
  funext i
  have h := congrFun (rvAppend_flip u.val v.val) (finAddFlip.symm i)
  simpa only [Function.comp_apply,Equiv.apply_symm_apply] using h

theorem rvProductAssocMap_labels (U : RVObject (M := M) S k) (V : RVObject (M := M) S l)
    (W : RVObject (M := M) S j) (x : (rvProductObject (rvProductObject U V) W).domain) :
    (rvProductAssocMap U V W x).val =
      fun i => x.val (Fin.cast (Nat.add_assoc U.arity V.arity W.arity).symm i) := by
  obtain ⟨uv,w,rfl⟩ := exists_rvPackPair (rvProductObject U V).domain W.domain x
  obtain ⟨u,v,rfl⟩ := exists_rvPackPair U.domain V.domain uv
  rw [rvProductAssocMap_pair]
  change Fin.append u.val (Fin.append v.val w.val) =
    fun i => Fin.append (Fin.append u.val v.val) w.val (Fin.cast (Nat.add_assoc U.arity V.arity W.arity).symm i)
  funext i
  have h := congrFun (Fin.append_assoc u.val v.val w.val) (Fin.cast (Nat.add_assoc U.arity V.arity W.arity).symm i)
  simpa only [Function.comp_apply,Fin.cast_cast,Fin.cast_refl,id_eq] using h.symm

theorem rvProductRightUnitMap_labels (U : RVObject (M := M) S k)
    (x : (rvProductObject U (rvUnitObject S)).domain) :
    (rvProductRightUnitMap U x).val = fun i => x.val (Fin.castAdd 0 i) := by
  obtain ⟨u,v,rfl⟩ := exists_rvPackPair U.domain (rvUnitObject S).domain x
  change (rvUnpack U.domain (rvUnitObject S).domain (rvPackPair U.domain (rvUnitObject S).domain u v)).val.1 = _
  rw [rvUnpack_pair]
  funext i
  change u.val i = Fin.append u.val v.val (Fin.castAdd 0 i)
  exact (Fin.append_left _ _ _).symm

end IntegrationInACVF.Section6
