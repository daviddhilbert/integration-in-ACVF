import IntegrationSection6.GammaVFCodePairing
import IntegrationSection6.GammaPreparedFamilies

/-! Prepare a finite RV code once. Any predicate determined by that code
then holds between inverse images of every pair with the same prepared key. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {S : Set M} {p : ℕ}

theorem gamma_prepare_vf_row_code {κ : Cardinal} (hs : Saturated M κ)
    (h00 : M ⊨ Axioms.ACVF00) (hsmall : Cardinal.mk B.real < κ)
    (FBase : VFFieldBase B.real) (hBS : B.real ⊆ S)
    (A : DefSet (M := M) S p 0) (hA : GammaSetDefinable B (carrier A))
    (P : (Fin p → M) → (Fin p → M) → Prop) (hCode : GammaVFRowCode B p P) :
    ∃ l : ℕ, ∃ C : DefSet (M := M) S p l, ∃ T : SpecialBijection A C,
      GammaChainDefinable B T.chain ∧ IsRVPullback (carrier C) ∧
      ∀ x y : C, SameRV x.val y.val →
        P (fun j => ((T.inverseMap x).val.1 j).val) (fun j => ((T.inverseMap y).val.1 j).val) := by
  obtain ⟨d,g,hg,hCode⟩ := hCode
  obtain ⟨l,C,T,hT,hC,hrows⟩ := gamma_prepare_finite_rv_families hs h00 hsmall FBase hBS A hA
    (fun _ : Fin 1 => d) (fun _ => pointMapGraph g) (fun _ => hg)
  refine ⟨l,C,T,hT,hC,?_⟩
  intro x y hxy
  let x₀ : PresentedSet.univ (pointSpace (M := M) p 0) B.real := ⟨(T.inverseMap x).val,Set.mem_univ _⟩
  let y₀ : PresentedSet.univ (pointSpace (M := M) p 0) B.real := ⟨(T.inverseMap y).val,Set.mem_univ _⟩
  have hx : pointMapGraph g (T.inverseMap x).val (g x₀).val := ⟨x₀,rfl,rfl⟩
  have hy := (hrows x y hxy 0 (g x₀).val).mp hx
  rcases hy with ⟨u,hu,hgu⟩
  have he : u = y₀ := Subtype.ext hu
  apply hCode x₀ y₀
  exact Subtype.ext (hgu.symm.trans (congrArg (fun v => (g v).val) he))

end IntegrationInACVF.Section6
