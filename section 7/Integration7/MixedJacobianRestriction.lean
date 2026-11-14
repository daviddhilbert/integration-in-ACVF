import Integration7.VFVolumeBijections

/-! Two defined mixed Jacobians agree when one actual definable map
is a restriction of the other. No definedness is asserted at boundary
points of either source. -/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n a b : ℕ}

theorem mixedVFJacobian_eq_of_restriction
    {A L : DefSet (rawMixedSpace (M := M) n a) S}
    {B R : DefSet (rawMixedSpace (M := M) n b) S}
    (hLA : L.carrier ⊆ A.carrier) (f : Map A B) (g : Map L R)
    (hfg : ∀ u : L, (f ⟨u.val, hLA u.property⟩).val = (g u).val)
    (p : L) {J K : VFType (M := M)}
    (hf : HasMixedVFJacobianAt f ⟨p.val, hLA p.property⟩ J)
    (hg : HasMixedVFJacobianAt g p K) : J = K := by
  obtain ⟨F, ⟨ρF, hF⟩, hJF⟩ := hf
  obtain ⟨G, ⟨ρG, hG⟩, hKG⟩ := hg
  have he : Set.EqOn F G (vfBall p.val.1 (max ρF ρG)) := by
    intro x hx
    obtain ⟨hxA, hxF⟩ := hF x (vfBall_anti (le_max_left _ _) hx)
    obtain ⟨hxL, hxG⟩ := hG x (vfBall_anti (le_max_right _ _) hx)
    have hsame : (⟨(x, p.val.2), hxA⟩ : A) =
        ⟨(x, p.val.2), hLA hxL⟩ := rfl
    have hval := (hxF.symm.trans ((congrArg (fun u : A => (f u).val) hsame).trans
      (hfg ⟨(x, p.val.2), hxL⟩))).trans hxG
    exact congrArg Prod.fst hval
  exact (hJF.congr_on_vfBall he).unique hKG

theorem preservesVFVolume_of_restriction
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) (hn : 0 < n)
    {A L : DefSet (rawMixedSpace (M := M) n a) (C.base : Set M)}
    {B R : DefSet (rawMixedSpace (M := M) n b) (C.base : Set M)}
    (hLA : L.carrier ⊆ A.carrier) (f : Map A B) (g : Map L R)
    (hfg : ∀ u : L, (f ⟨u.val, hLA u.property⟩).val = (g u).val)
    (ω : VolumeForm A) (π : VolumeForm B) (ω' : VolumeForm L) (π' : VolumeForm R)
    (hω : ∀ u : L, ω.value ⟨u.val, hLA u.property⟩ = ω'.value u)
    (hπ : ∀ u : L, π.value (f ⟨u.val, hLA u.property⟩) = π'.value (g u))
    (hf : PreservesVFVolume ω π f) : PreservesVFVolume ω' π' g := by
  letI : CharZero (VFType (M := M)) := Section6.vfCharZero_of_model00 C.model00
  let i : Map L A := Map.inclusion hLA
  have hi : Function.Injective i := by
    intro p q he
    exact Subtype.ext (congrArg (fun u : A => u.val) he)
  have hglobal := VFAlmostEverywhere.pullback_injective i hi hf
  obtain ⟨D, hDL, hd, hD⟩ := lemma_9_12_ae hc C.uncountable.le C.saturated C.small hn
    (Map.id L) g (Map.finiteFibres_of_injective Function.injective_id)
  have hlocal : VFAlmostEverywhere L (fun p => ∃ K : VFType (M := M),
      HasMixedVFJacobianAt g p K) := by
    refine ⟨D, hDL, hd, ?_⟩
    intro p hp
    obtain ⟨J, K, _, hK, _⟩ := hD p hp
    exact ⟨K, hK⟩
  apply (vfAlmostEverywhere_and hc C hglobal hlocal).mono
  rintro p ⟨⟨J, hJ, hφ⟩, K, hK⟩
  have he := mixedVFJacobian_eq_of_restriction hLA f g hfg p hJ hK
  refine ⟨K, hK, ?_⟩
  simpa only [i, Map.inclusion, hω, hπ, he] using hφ

end IntegrationInACVF.Section7
