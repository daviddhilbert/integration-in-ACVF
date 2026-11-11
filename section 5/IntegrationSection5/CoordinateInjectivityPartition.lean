import IntegrationSection5.CoordinateInjectivityRefinement
import IntegrationSection5.ScalarTagPartition

/-! Constructed finite Gamma-definable pieces with an injective target
coordinate on every fixed-context, fixed-code source-head fibre. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5 SpecialTransformations.Section3
open IntegrationInACVF.Section4
namespace IntegrationInACVF.Section5
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {S : Set M} {p m u w : ℕ}

theorem coordinate_injective_rv_partition {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00) (G : GammaParameters.Base (M := M))
    (hsmall : Cardinal.mk G.real < κ) (δ : Values.Gamma (M := M)) (hδ : 1 < δ)
    (A : DefSet (M := M) S (p+1) m) (hA : GammaSetDefinable G (carrier A))
    {B : DefSet (M := M) S u w} (hu : 0 < u) (f : Map A B) (hbij : Function.Bijective f)
    (hf : GammaGraphDefinable G (pointMapGraph f)) :
    ∃ r : ℕ, ∃ R : GammaRVMap G (carrier A) r,
      ∃ P : Option (Fin u) → Set (Point (M := M) (p+1) m),
        (∀ i, GammaSetDefinable G (P i)) ∧
        (∀ i, P i ⊆ carrier A) ∧
        (∀ i k, i ≠ k → Disjoint (P i) (P k)) ∧
        (∀ a : A, ∃ i, a.val ∈ P i) ∧
        ∀ i, ∃ j : Fin u, ∀ b c : A, b.val ∈ P i → c.val ∈ P i →
          MixedScalarFamilies.context b.val = MixedScalarFamilies.context c.val →
          R.toFun b = R.toFun c → vfAt (f b).val j = vfAt (f c).val j → b = c := by
  obtain ⟨d,Q,j,hQ⟩ := coordinate_scalar_refinement hκ hs h00 G hsmall δ hδ A hA f hf
  obtain ⟨r,R,hRQ,hSingle⟩ := refine_all_constant_fibres hκ hs h00 G hsmall f hbij hf Q j hQ
  refine ⟨r,R,scalarTagPiece Q j,scalarTagPiece_definable Q j,
    scalarTagPiece_subset Q j,(fun _ _ h => scalarTagPiece_disjoint Q j h),
    scalarTagPiece_cover Q j,?_⟩
  intro i
  cases i with
  | none =>
    refine ⟨⟨0,hu⟩,?_⟩
    intro b c hb _ hctx hcode _
    exact (hSingle b ((mem_allConstantDomain Q j b).mp hb) c hctx.symm hcode.symm).symm
  | some i =>
    refine ⟨i,?_⟩
    intro b c hb _ hctx hcode hscalar
    have htag := ((mem_scalarTagPiece_some Q j i b).mp hb).2
    rcases hQ i b with ⟨hz,_⟩ | ⟨_,hinj⟩
    · exact (htag hz).elim
    · exact hinj b c rfl hctx.symm rfl (hRQ c b hcode.symm) hscalar

end IntegrationInACVF.Section5
