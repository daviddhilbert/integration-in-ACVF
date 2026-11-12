import IntegrationSection6.FiniteGammaIsomorphisms

/-! Reconstruct actual RV[k] isomorphisms from full original-Gamma
relations satisfying totality, uniqueness, bijectivity and weight balance. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
namespace IntegrationInACVF.Section6.FiniteRV
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {n : ℕ}

def gammaIsoOfFiniteRelation (U V : GammaRVFiniteObject B n)
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
      H u.val v.val → rawWeight (rawVolume U u) = rawWeight (rawVolume V v)) :
    GammaRVIso U.toGammaRVObject V.toGammaRVObject := by
  let f (u : rvObjectDomain U.object) : rvObjectDomain V.object := (hfun u).exists.choose
  have hf (u) : H u.val (f u).val := (hfun u).exists.choose_spec
  have hb : Function.Bijective f := by
    constructor
    · intro u u' he
      exact hinj u u' (f u) (hf u) (he.symm ▸ hf u')
    · intro v
      obtain ⟨u,hu⟩ := hsurj v
      exact ⟨u,(hfun u).unique (hf u) hu⟩
  let e := Equiv.ofBijective f hb
  refine gammaIsoOfFiniteEquiv U V e ?_ (fun u => hw u (f u) (hf u))
  apply GammaGraphDefinable.congr hH
  intro p q
  constructor
  · intro hpq
    obtain ⟨⟨u,hu⟩,⟨v,hv⟩⟩ := hdom p.2 q.2 hpq
    have huv : H u.val v.val := by simpa only [hu,hv] using hpq
    exact ⟨u,hu,congrArg Subtype.val ((hfun u).unique (hf u) huv) |>.trans hv⟩
  · rintro ⟨u,hu,hv⟩
    change (f u).val = q.2 at hv
    simpa only [hu,hv] using hf u

end IntegrationInACVF.Section6.FiniteRV
