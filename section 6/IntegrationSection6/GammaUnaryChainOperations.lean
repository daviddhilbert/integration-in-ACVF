import IntegrationSection5.GammaUnaryRestriction
import IntegrationSection5.UnaryFactorizations
import IntegrationSection5.GammaChainAlgebra

/-! Inverses and actual special-chain factorizations for Gamma unary
chains. All maps retain their original parameter graphs. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5
open IntegrationInACVF.Section5
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {S : Set M} {n a b : ℕ}

def gammaUnaryChainInverse {U : Set (Point (M := M) n a)} {V : Set (Point (M := M) n b)}
    (T : GammaUnaryChain B n U V) : GammaUnaryChain B n V U := by
  induction T with
  | nil U hU => exact .nil U hU
  | @cons a c b U W V i e hi tail ih =>
    let er := e.symm (gammaLogicInput B)
    have hU := er.target_definable (gammaLogicInput B)
    have hr : ∀ w : W, ∀ j : Fin n, j ≠ i → (er.equiv w).val.1 j = w.val.1 j := by
      intro w j hj
      change (e.equiv.symm w).val.1 j = w.val.1 j
      simpa only [Equiv.apply_symm_apply] using (hi (e.equiv.symm w) j hj).symm
    exact ih.append (.cons i er hr (.nil U hU))

theorem gamma_special_unary_chain_exists (hn : 0 < n)
    {U : DefSet (M := M) S n a} {V : DefSet (M := M) S n b}
    (T : Chain S n U V) (hT : GammaChainDefinable B T) :
    ∃ t : GammaUnaryChain B n (carrier U) (carrier V),
      ∀ u : U, (t.toIso.equiv u).val = (T.toMap u).val := by
  induction T with
  | nil U => exact ⟨.nil (carrier U) hT,fun _ => rfl⟩
  | cons p tail ih =>
    obtain ⟨t,ht⟩ := ih hT.2
    let e : GammaIso B _ _ := ⟨Equiv.ofBijective p.toMap p.bijective,
      GammaPrimitiveDefinable.graph (gammaLogicInput B) p hT.1⟩
    exact ⟨.cons (primitiveUnaryCoordinate hn p) e (primitive_unaryRelative hn p) t,
      fun u => ht (p.toMap u)⟩

end IntegrationInACVF.Section6
