import IntegrationSection5.GammaScalarUpdate
import IntegrationSection5.RVAttachment
import IntegrationSection5.MixedScalarFamilies
import IntegrationSection5.GammaUnaryChain

/-! RV attachment followed by an injective active-coordinate replacement. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5 SpecialTransformations.Section3
open IntegrationInACVF.Section4
namespace IntegrationInACVF.Section5
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {G : GammaParameters.Base (M := M)} {p m d : ℕ}
variable {A : Set (Point (M := M) (p+1) m)}

theorem context_replace_head (q : Point (M := M) (p+1) m) (x : VF (M := M)) :
    MixedScalarFamilies.context (replace 0 q x) = MixedScalarFamilies.context q := by
  apply congrArg gammaPointCode
  refine Prod.ext ?_ rfl
  funext i
  change (Function.update q.1 0 x) i.succ = q.1 i.succ
  exact Function.update_of_ne (Fin.succ_ne_zero i) _ _

def codedHeadUpdate (Q : GammaRVMap G A d) (g : A → VF (M := M)) (a : A) :
    Point (M := M) (p+1) (m+d) := replace 0 (Q.attachment a) (g a)

theorem codedHeadUpdate_injective (Q : GammaRVMap G A d) (g : A → VF (M := M))
    (hinj : ∀ a b : A, MixedScalarFamilies.context a.val = MixedScalarFamilies.context b.val →
      Q.toFun a = Q.toFun b → g a = g b → a = b) :
    Function.Injective (codedHeadUpdate Q g) := by
  intro a b hab
  have hc : MixedScalarFamilies.context (Q.attachment a) = MixedScalarFamilies.context (Q.attachment b) := by
    rw [← context_replace_head (Q.attachment a) (g a),← context_replace_head (Q.attachment b) (g b)]
    exact congrArg MixedScalarFamilies.context hab
  obtain ⟨hc,hQ⟩ := (RVAttachment.context_eq_iff Q a b).mp hc
  apply hinj a b hc hQ
  have h := congrArg (fun q : Point (M := M) (p+1) (m+d) => q.1 0) hab
  simpa only [codedHeadUpdate,replace,Function.update_self] using h

/-- Both steps are actual original-Gamma bijections; the result is an actual
GammaUnaryChain, which has a checked realization as a definable UnaryChain. -/
theorem coded_head_unary_factorization (Q : GammaRVMap G A d) (g : A → VF (M := M))
    (hg : GammaScalarGraphDefinable G (fun p y => ∃ a : A, a.val = p ∧ g a = y))
    (hinj : ∀ a b : A, MixedScalarFamilies.context a.val = MixedScalarFamilies.context b.val →
      Q.toFun a = Q.toFun b → g a = g b → a = b) :
    ∃ C : Set (Point (M := M) (p+1) (m+d)), ∃ T : GammaUnaryChain G (p+1) A C,
      ∀ a : A, (T.toIso.equiv a).val = codedHeadUpdate Q g a := by
  let e := RVAttachment.gammaIso Q
  let E := RVAttachment.target Q
  let g' : E → VF (M := M) := fun b => g (e.equiv.symm b)
  have hg' : GammaScalarGraphDefinable G (fun p y => ∃ b : E, b.val = p ∧ g' b = y) :=
    gamma_iso_precomp_scalar (e.symm (gammaLogicInput G)) g hg
  have hinj' : Function.Injective (fun b : E => replace 0 b.val (g' b)) := by
    intro b c heq
    have hb : Q.attachment (e.equiv.symm b) = b.val := congrArg Subtype.val (e.equiv.apply_symm_apply b)
    have hc : Q.attachment (e.equiv.symm c) = c.val := congrArg Subtype.val (e.equiv.apply_symm_apply c)
    have h : codedHeadUpdate Q g (e.equiv.symm b) = codedHeadUpdate Q g (e.equiv.symm c) := by
      change replace 0 (Q.attachment _) _ = replace 0 (Q.attachment _) _
      rw [hb,hc]
      exact heq
    exact e.equiv.symm.injective (codedHeadUpdate_injective Q g hinj h)
  let u := scalarUpdateIso (G := G) (0 : Fin (p+1)) g' hg' hinj'
  refine ⟨scalarUpdateTarget 0 g',.cons 0 e (fun a j _ => rfl)
    (.cons 0 u (scalarUpdateIso_unary 0 g' hg' hinj')
      (.nil _ (u.target_definable (gammaLogicInput G)))),?_⟩
  intro a
  change replace 0 (Q.attachment a) (g (e.equiv.symm (e.equiv a))) = _
  rw [e.equiv.symm_apply_apply]
  rfl

end IntegrationInACVF.Section5
