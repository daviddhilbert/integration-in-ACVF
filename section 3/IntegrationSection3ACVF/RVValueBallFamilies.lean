import IntegrationSection3ACVF.RVValueShellGeometry
import IntegrationSection3ACVF.AtomicBallFamilyChoice

/-! Nonalgebraic actual RV-fibre balls in a fixed value shell. -/

set_option backward.isDefEq.respectTransparency false

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open IntegrationInACVF.Section3
open IntegrationInACVF.Section3ACVF.GammaRadiusAtomicity
open IntegrationInACVF.Section3ACVF.BallCosetAtomicity
open IntegrationInACVF.Section3ACVF.RVValueShellGeometry

namespace IntegrationInACVF.Section3ACVF.RVValueBallFamilies

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

def family (H : AddSubgroup (VFType (M := M))) (γ : Values.Gamma (M := M)) :=
  BetaSubballFamilies.family H (shell γ)

theorem definable (B : FullBaseAtomicity.Base (M := M))
    (H : AddSubgroup (VFType (M := M)))
    (hH : FullBaseAtomicity.OverBase B
      {z : Fin 1 → M | z 0 ∈ Subtype.val '' (H : Set (VFType (M := M)))})
    (γ : Values.Gamma (M := M)) (hγ : FullGammaSyntax.Scalar B {γ}) :
    FullBaseAtomicity.Family B (family H γ) := by
  exact BetaSubballFamilies.definable B H hH (FullGammaRadius.rv_preimage hγ)

theorem member_fibre (H : AddSubgroup (VFType (M := M)))
    (γ : Values.Gamma (M := M))
    (hH : ∀ a : VFType (M := M), cosetBody H a = gammaBall a γ true)
    {i : BallImaginaries.Ball M} (hi : i ∈ family H γ) :
    ∃ r : VFType (M := M), Values.vfValueHom r = γ.val ∧
      BallImaginaries.underlying i = fibre (CanonicalRV.encodedRv r) := by
  obtain ⟨r,hr⟩ := BetaSubballFamilies.member_presentation H γ hH hi
  have hsub : BallImaginaries.underlying i ⊆ shell γ := hi.2
  have hval : Values.vfValueHom r = γ.val := (shell_mem r γ).mp
    (hsub (hr.symm ▸ BallEnlargementGeometry.gammaBall_centre_mem r γ true))
  exact ⟨r,hval,hr.trans (gammaBall_eq_fibre r γ hval)⟩

theorem cover (H : AddSubgroup (VFType (M := M)))
    (γ : Values.Gamma (M := M))
    (hH : ∀ a : VFType (M := M), cosetBody H a = gammaBall a γ true) :
    ∀ x ∈ shell γ, ∃ i ∈ family H γ, x ∈ BallImaginaries.underlying i := by
  intro x hx
  let x' : VFType (M := M) := ⟨x,hx.1⟩
  have hxγ := (shell_mem x' γ).mp hx
  obtain ⟨i,hi⟩ := GammaCosetGeometry.gammaBall_coded x' γ
  refine ⟨i,⟨?_,?_⟩,?_⟩
  · exact ⟨x,x'.property,hi.trans ((hH x').symm.trans (cosetRelation_fibre H x').symm)⟩
  · change BallImaginaries.underlying i ⊆ shell γ
    rw [hi]
    exact gammaBall_subset_shell x' γ hxγ
  · rw [hi]
    exact BallEnlargementGeometry.gammaBall_centre_mem x' γ true

theorem infinite (h00 : M ⊨ Axioms.ACVF00)
    (H : AddSubgroup (VFType (M := M))) (γ : Values.Gamma (M := M))
    (hH : ∀ a : VFType (M := M), cosetBody H a = gammaBall a γ true) :
    (family H γ).Infinite := by
  intro hFin
  apply rv_image_infinite h00 γ
  apply QuotientCover.image_finite_of_finite_cover CanonicalRV.encodedRv hFin
    (fun i => {x : VFType (M := M) | x.val ∈ BallImaginaries.underlying i})
  · intro i hi x hx y hy
    obtain ⟨r,_,hr⟩ := member_fibre H γ hH hi
    rw [hr] at hx hy
    exact Subtype.ext (hx.2.trans hy.2.symm)
  · intro x hx
    exact cover H γ hH x.val hx

theorem exists_atomic_fibre {κ : Cardinal} (hs : Saturated M κ)
    (B : FullBaseAtomicity.Base (M := M)) (hB : B.imaginary = ∅)
    (hsmall : Cardinal.mk B.real < κ) (h00 : M ⊨ Axioms.ACVF00)
    (γ : Values.Gamma (M := M)) (hγ : FullGammaSyntax.Scalar B {γ}) :
    ∃ (i : BallImaginaries.Ball M) (t : CanonicalRV.RVSort M),
      t.val ≠ iRVZero ∧ Values.vrv t = γ.val ∧
      BallImaginaries.underlying i = fibre t ∧
      AdjoinBall.AtomicOver (B.adjoin (Sum.inl i)) (fibre t) := by
  obtain ⟨H,hH,hcosets⟩ := FullGammaRadius.gamma_subgroup B γ hγ true
  have hd := definable B H hH γ hγ
  have hInf := infinite h00 H γ hcosets
  have hdis := BetaSubballFamilies.disjoint H (shell γ)
  have hne (i : BallImaginaries.Ball M) (_ : i ∈ family H γ) :
      (BallImaginaries.underlying i).Nonempty :=
    CanonicalBallSupport.encodedBall_nonempty (BallCodeGeometry.underlying_isBall i)
  obtain ⟨i,hi,hat⟩ := AtomicBallFamilyChoice.exists_atomic hs B hB hsmall (family H γ) hd hInf hne hdis
  obtain ⟨r,hrγ,hiR⟩ := member_fibre H γ hcosets hi
  have ht0 : (CanonicalRV.encodedRv r).val ≠ iRVZero := by
    intro he
    exact γ.property (hrγ.symm.trans ((Values.vrv_eq_infinity_iff _).mpr he))
  exact ⟨i,CanonicalRV.encodedRv r,ht0,hrγ,hiR,hiR ▸ hat⟩

end IntegrationInACVF.Section3ACVF.RVValueBallFamilies
