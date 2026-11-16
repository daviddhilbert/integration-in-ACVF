module

public import Integration7.VFVolumeBijections
public import Integration7.VFAlmostEverywhere

@[expose] public section

/-! The mixed VF Jacobian is unchanged by altering only the output RV
labels. Generic charts for the new labels are constructed by the checked
mixed differentiability theorem. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n a b c : ℕ}

theorem mixedVFJacobian_eq_of_vf_eq
    {A : Set ((Fin n → VFType (M := M)) × (Fin a → CanonicalRV.RVSort M))}
    {B : Set ((Fin n → VFType (M := M)) × (Fin b → CanonicalRV.RVSort M))}
    {D : Set ((Fin n → VFType (M := M)) × (Fin c → CanonicalRV.RVSort M))}
    (f : A → B) (g : A → D) (hVF : ∀ p, (f p).val.1 = (g p).val.1)
    (p : A) {J K : VFType (M := M)}
    (hJ : HasMixedVFJacobianAt f p J) (hK : HasMixedVFJacobianAt g p K) : J = K := by
  obtain ⟨F,⟨ρ,hF⟩,hJ⟩ := hJ
  obtain ⟨G,⟨σ,hG⟩,hK⟩ := hK
  have he : Set.EqOn F G (vfBall p.val.1 (max ρ σ)) := by
    intro x hx
    obtain ⟨hp,hFx⟩ := hF x (vfBall_anti (le_max_left _ _) hx)
    obtain ⟨hq,hGx⟩ := hG x (vfBall_anti (le_max_right _ _) hx)
    exact (congrArg Prod.fst hFx).symm.trans
      ((hVF ⟨(x,p.val.2),hp⟩).trans (congrArg Prod.fst hGx))
  exact (hJ.congr_on_vfBall he).unique hK

theorem vfJacobianOne_of_same_vf
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) (hn : 0 < n)
    {A : DefSet (rawMixedSpace (M := M) n a) (C.base : Set M)}
    {B : DefSet (rawMixedSpace (M := M) n b) (C.base : Set M)}
    {D : DefSet (rawMixedSpace (M := M) n c) (C.base : Set M)}
    (f : Map A B) (g : Map A D) (hVF : ∀ p, (f p).val.1 = (g p).val.1)
    (hf : VFAlmostEverywhere A (fun p => HasMixedVFJacobianAt f p 1)) :
    VFAlmostEverywhere A (fun p => HasMixedVFJacobianAt g p 1) := by
  letI : CharZero (VFType (M := M)) := Section6.vfCharZero_of_model00 C.model00
  obtain ⟨E,hEA,hd,hE⟩ := lemma_9_12_ae hc C.uncountable.le C.saturated C.small hn
    (Map.id A) g (Map.finiteFibres_of_injective Function.injective_id)
  have hg : VFAlmostEverywhere A (fun p => ∃ J, HasMixedVFJacobianAt g p J) :=
    ⟨E,hEA,hd,by
      intro p hp
      obtain ⟨J,K,_,hK,_⟩ := hE p hp
      exact ⟨K,hK⟩⟩
  apply (vfAlmostEverywhere_and hc C hf hg).mono
  rintro p ⟨h1,K,hK⟩
  have he := mixedVFJacobian_eq_of_vf_eq f g hVF p h1 hK
  exact he ▸ hK

end IntegrationInACVF.Section7
