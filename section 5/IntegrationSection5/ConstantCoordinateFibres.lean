import IntegrationSection5.ScalarCoordinateRefinement
import IntegrationSection5.FixedVFFiniteImage

/-! For a bijection, a source-code fibre on which all target VF coordinates
are constant has only finitely many possible active source VF values. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5 SpecialTransformations.Section3
open IntegrationInACVF.Section4
namespace IntegrationInACVF.Section5
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {S : Set M} {p m u w d : ℕ}
variable {A : DefSet (M := M) S (p+1) m} {B : DefSet (M := M) S u w}

theorem all_constant_code_fibre_finite {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (G : GammaParameters.Base (M := M))
    (hsmall : Cardinal.mk G.real < κ) (f : Map A B) (hbij : Function.Bijective f)
    (hf : GammaGraphDefinable G (pointMapGraph f))
    (Q : GammaRVMap G (carrier A) d) (j : Fin u → Fin d)
    (hQ : ∀ i : Fin u, TaggedScalarRefinement Q (j i) (fun a => vfAt (f a).val i))
    (a₀ : A) (hzero : ∀ i : Fin u, Q.toFun a₀ (j i) = rv (0 : VF (M := M))) :
    {x : VF (M := M) | ∃ a : A,
      MixedScalarFamilies.context a.val = MixedScalarFamilies.context a₀.val ∧
        Q.toFun a = Q.toFun a₀ ∧ vfAt a.val 0 = x}.Finite := by
  let g : B → VF (M := M) := fun b => vfAt (Map.inverse f hbij b).val 0
  have hg : GammaScalarGraphDefinable G (fun q y => ∃ b : B, b.val = q ∧ g b = y) :=
    gamma_scalar_coordinate (Map.inverse f hbij) (gamma_inverse_map_graph f hbij hf) 0
  have hFin := fixed_vf_scalar_image_finite hκ hs G hsmall (carrier B) g hg (f a₀).val.1
  apply hFin.subset
  rintro x ⟨a,hctx,hcode,hx⟩
  refine ⟨f a,funext fun i => ?_,?_⟩
  · rcases hQ i a₀ with ⟨_,hconst⟩ | ⟨htag,_⟩
    · exact hconst a hctx hcode
    · exact (GammaRVMap.zero_ne_one ((hzero i).symm.trans htag)).elim
  · change vfAt (Map.inverse f hbij (f a)).val 0 = x
    rw [Map.inverse_apply]
    exact hx

end IntegrationInACVF.Section5
