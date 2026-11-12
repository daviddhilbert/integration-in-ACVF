import IntegrationSection6.LiftCarrierGeometry
import IntegrationSection6.ElementaryPacking

/-! Exact equality of the canonical RV key image after a full-locus
centripetal step and the elementary-blowup key domain. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
  SpecialTransformations.Section4.rawRVSpace SpecialTransformations.DefinableGeometry.Space.ofEmbedding

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section5

namespace IntegrationInACVF.Section6

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {S : Set M} {n : ℕ}

def focusKeyImage {U : RVObject (M := M) S n}
    {A : SpecialTransformations.Section5.DefSet (M := M) S n U.arity}
    {i : Fin n} {k : Fin U.arity} (D : Focus A i k) :
    Set (Fin (n+U.arity) → CanonicalRV.RVSort M) :=
  {r | ∃ a : A, Fin.append (fun j => rv ((D.toFocusGeometry.eta a.val).1 j)) a.val.2 = r}

/-- This is the complete image computation in6.9. It keeps all old labels
and includes the absorbing blowup parameter, which represents the centre. -/
theorem focusKeyImage_eq_elementary {U : RVObject (M := M) S n}
    {A : SpecialTransformations.Section5.DefSet (M := M) S n U.arity}
    (h : PresentsLift U A) {i : Fin n} {k : Fin U.arity}
    (D : Focus A i k) (hfull : carrier A ⊆ D.locus)
    (hnz : ∀ u : U.domain, U.value u i ≠ 0) :
    focusKeyImage D = (elementaryKeyObject U i).domain.carrier := by
  ext r
  constructor
  · rintro ⟨a,rfl⟩
    obtain ⟨u,hu,hvol⟩ := (h a.val).mp a.property
    have hai : a.val.1 i ≠ (0 : VF (M := M)) := by
      intro he
      apply hnz u
      exact (congrFun hvol i).trans (he ▸ RVOperations.rv_zero)
    have hc := D.toFocusGeometry.center_sameRV a.val ⟨a.property,hfull a.property⟩
    let c := D.center a.val
    have hc0 : c ≠ 0 := fullFocus_center_nonzero D hfull a hai
    let q := translatedFibreEquiv c hc0 ⟨a.val.1 i,hc.symm⟩
    let s : positiveRV (M := M) S :=
      ⟨![q.val.2],(positiveRV_iff_absolute_lt_one _).mpr q.property.2⟩
    let b : (elementary U i).domain := rvPackPair U.domain (positiveRV S) u s
    refine ⟨b,?_⟩
    change (elementaryKeyMap U i b).val = _
    rw [elementaryKeyMap_value,elementary_value,elementaryProjection_pair,elementaryParameter_pair]
    apply congrArg₂ rvAppend ?_ hu
    funext j
    by_cases hj : j = i
    · subst j
      rw [blowupValue_same]
      have heta : (D.toFocusGeometry.eta a.val).1 i = vfAt a.val i - c := by
        simp [FocusGeometry.eta,hfull a.property,replace,c,vfAt]
      rw [heta]
      have hq := q.property.1
      have he : rv c = U.value u i := hc.trans (congrFun hvol i).symm
      exact (hq.trans (congrArg (fun t => q.val.2*t) he)).symm
    · rw [blowupValue_other i _ _ j hj,D.toFocusGeometry.eta_other a.val j hj]
      exact congrFun hvol j
  · rintro ⟨b,hb⟩
    obtain ⟨u,s,rfl⟩ := exists_rvPackPair U.domain (positiveRV S) b
    obtain ⟨p,hp,hpvol⟩ := h.representative u
    let β := blowupValue i (U.value u) (s.val 0)
    obtain ⟨x,hx⟩ := tupleRV_surjective β
    have hpi : p.val.1 i ≠ (0 : VF (M := M)) := by
      intro he
      apply hnz u
      exact (congrFun hpvol i).symm.trans (he ▸ RVOperations.rv_zero)
    have hbs : CanonicalRV.encodedRv (x i) = (s.val 0) * CanonicalRV.encodedRv (p.val.1 i) := by
      have he := congrFun hx i
      change rv (x i) = β i at he
      rw [show β i = s.val 0 * U.value u i from blowupValue_same i _ _] at he
      exact he.trans (congrArg (fun t => s.val 0*t) (congrFun hpvol i).symm)
    obtain ⟨a,ha,heta⟩ := fullFocus_fibre_surjective D h.pullback hfull p hpi (x i) (s.val 0)
      hbs ((positiveRV_iff_absolute_lt_one _).mp s.property)
    refine ⟨a,?_⟩
    rw [← hb]
    change _ = (elementaryKeyMap U i (rvPackPair U.domain (positiveRV S) u s)).val
    rw [elementaryKeyMap_value,elementary_value,elementaryProjection_pair,elementaryParameter_pair]
    apply congrArg₂ rvAppend ?_ ((congrArg Prod.snd ha).trans hp)
    rw [heta]
    funext j
    by_cases hj : j = i
    · subst j
      have hxi := congrFun hx i
      change rv (x i) = β i at hxi
      simpa only [replace,Function.update_self,β,blowupValue_same] using hxi
    · simpa [replace,hj,β,blowupValue,if_neg hj] using congrFun hpvol j

end IntegrationInACVF.Section6
