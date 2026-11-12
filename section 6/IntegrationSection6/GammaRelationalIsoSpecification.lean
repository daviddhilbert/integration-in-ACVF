import IntegrationSection6.GammaFiniteGraphIsomorphisms

/-! The actual relational isomorphism factory realizes its given relation
at every source point. This exposes its checked choice specification for
uniform indexed chart assembly. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
namespace IntegrationInACVF.Section6.FiniteRV
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {n : ℕ}

theorem gammaIsoOfFiniteRelation_apply (U V : GammaRVFiniteObject B n)
    (H : (Fin (rvObjectArity U.object) → RV (M := M)) →
      (Fin (rvObjectArity V.object) → RV (M := M)) → Prop)
    (hH : GammaGraphDefinable B (fun (p : Point (M := M) 0 (rvObjectArity U.object))
      (q : Point (M := M) 0 (rvObjectArity V.object)) => H p.2 q.2))
    (hdom : ∀ x y, H x y →
      (∃ u : rvObjectDomain U.object, u.val = x) ∧
      (∃ v : rvObjectDomain V.object, v.val = y))
    (hfun : ∀ u : rvObjectDomain U.object, ∃! v : rvObjectDomain V.object, H u.val v.val)
    (hinj : ∀ u u' : rvObjectDomain U.object, ∀ v : rvObjectDomain V.object,
      H u.val v.val → H u'.val v.val → u = u')
    (hsurj : ∀ v : rvObjectDomain V.object, ∃ u : rvObjectDomain U.object, H u.val v.val)
    (hw : ∀ u : rvObjectDomain U.object, ∀ v : rvObjectDomain V.object,
      H u.val v.val → rawWeight (rawVolume U u) = rawWeight (rawVolume V v))
    (u : rvObjectDomain U.object) :
    H u.val ((gammaIsoOfFiniteRelation U V H hH hdom hfun hinj hsurj hw).equiv u).val :=
  (hfun u).exists.choose_spec

end IntegrationInACVF.Section6.FiniteRV
