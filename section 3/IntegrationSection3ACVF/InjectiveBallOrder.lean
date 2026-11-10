import IntegrationSection3ACVF.OpenBallSeparationGeometry
import IntegrationSection3ACVF.OpenSubballImages

/-! An injective definable VF map on an atomic open ball preserves
strict comparisons of valuations of differences from a fixed point. -/

set_option backward.isDefEq.respectTransparency false

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open IntegrationInACVF.Section3
open IntegrationInACVF.Section3ACVF.GammaRadiusAtomicity

namespace IntegrationInACVF.Section3ACVF.InjectiveBallOrder

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem value_strictMono (B : FullBaseAtomicity.Base (M := M))
    (h00 : M ⊨ Axioms.ACVF00) (δ : Values.Gamma (M := M))
    (hδ : FullGammaSyntax.Scalar B {δ}) (hδ1 : 1 < δ)
    {A : Set M} (ho : PaperBalls.IsOpenBall A) (hA : AdjoinBall.AtomicOver B A)
    (f : M → M) (hf : FullBaseAtomicity.OverBase B (ImaginaryBaseImages.graphOn A f))
    (hfVF : ∀ x ∈ A, iVF (f x)) (hinj : Set.InjOn f A)
    (x y z : VFType (M := M)) (hx : x.val ∈ A) (hy : y.val ∈ A) (hz : z.val ∈ A)
    (hdist : Values.vfValueHom (y-x) < Values.vfValueHom (z-x)) :
    let fx : VFType (M := M) := ⟨f x.val,hfVF _ hx⟩
    let fy : VFType (M := M) := ⟨f y.val,hfVF _ hy⟩
    let fz : VFType (M := M) := ⟨f z.val,hfVF _ hz⟩
    Values.vfValueHom (fy-fx) < Values.vfValueHom (fz-fx) := by
  let fx : VFType (M := M) := ⟨f x.val,hfVF _ hx⟩
  let fy : VFType (M := M) := ⟨f y.val,hfVF _ hy⟩
  let fz : VFType (M := M) := ⟨f z.val,hfVF _ hz⟩
  change Values.vfValueHom (fy-fx) < Values.vfValueHom (fz-fx)
  have hγ : Values.vfValueHom (y-x) ≠ Values.infinity := by
    intro h
    exact not_lt_of_ge (Values.le_infinity (Values.vfValueHom (z-x))) (h ▸ hdist)
  let γ : Values.Gamma (M := M) := ⟨Values.vfValueHom (y-x),hγ⟩
  let P := gammaBall x γ true
  have hxP : x.val ∈ P := BallEnlargementGeometry.gammaBall_centre_mem x γ true
  have hzP : z.val ∈ P := by
    change ∃ hz : iVF z.val, γ.val ≤ Values.vfValueHom (z-x) ∧
      (true = true → ¬ Values.vfValueHom (z-x) ≤ γ.val)
    exact ⟨z.property,hdist.le,fun _ => not_le_of_gt hdist⟩
  have hyP : y.val ∉ P := by
    intro h
    change ∃ hy : iVF y.val, γ.val ≤ Values.vfValueHom (y-x) ∧
      (true = true → ¬ Values.vfValueHom (y-x) ≤ γ.val) at h
    exact h.choose_spec.2 rfl le_rfl
  have hBall : IsBall A := by
    rcases ho with h | ⟨a,β,h⟩
    · exact Or.inl h
    · rw [h]
      exact BallEnlargementGeometry.gammaBall_isBall a β true
  have hPA : P ⊆ A := by
    rcases encodedBalls_laminar P (BallEnlargementGeometry.gammaBall_isBall x γ true) A hBall
      with h | h | h
    · exact h
    · exact (hyP (h hy)).elim
    · exact (Set.disjoint_left.mp h hxP hx).elim
  obtain ⟨i,hi⟩ := GammaCosetGeometry.gammaBall_coded x γ
  have hOpen : PaperBalls.IsOpenBall (BallImaginaries.underlying i) := Or.inr ⟨x,γ,hi⟩
  have hsub : BallImaginaries.underlying i ⊆ A := by rw [hi]; exact hPA
  have hImage := OpenSubballImages.image_open_of_atomic B h00 δ hδ hδ1 hA f hf hfVF hinj i hOpen hsub
  have hxI : x.val ∈ BallImaginaries.underlying i := hi.symm ▸ hxP
  have hzI : z.val ∈ BallImaginaries.underlying i := hi.symm ▸ hzP
  have hyImage : fy.val ∉ f '' BallImaginaries.underlying i := by
    rintro ⟨u,hu,he⟩
    have hEq : u = y.val := hinj (hsub hu) hy he
    have hyI : y.val ∈ BallImaginaries.underlying i := hEq ▸ hu
    rw [hi] at hyI
    exact hyP hyI
  exact OpenBallSeparationGeometry.inside_value_lt_outside hImage fx fy fz
    ⟨x.val,hxI,rfl⟩ hyImage ⟨z.val,hzI,rfl⟩

end IntegrationInACVF.Section3ACVF.InjectiveBallOrder
