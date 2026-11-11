import IntegrationSection5.CodedHeadUpdate
import IntegrationSection5.CoordinateContext

/-! Constructed relatively unary coding and replacement at any VF coordinate. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5 SpecialTransformations.Section3
open IntegrationInACVF.Section4
namespace IntegrationInACVF.Section5
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {G : GammaParameters.Base (M := M)} {n m d : ℕ}
variable {A : Set (Point (M := M) n m)}

def codedCoordinateUpdate (Q : GammaRVMap G A d) (i : Fin n) (g : A → VF (M := M)) (a : A) :
    Point (M := M) n (m+d) := replace i (Q.attachment a) (g a)

theorem codedCoordinateUpdate_injective (Q : GammaRVMap G A d) (i : Fin n) (g : A → VF (M := M))
    (hinj : ∀ a b : A, SameCoordinateContext i a.val b.val →
      Q.toFun a = Q.toFun b → g a = g b → a = b) :
    Function.Injective (codedCoordinateUpdate Q i g) := by
  intro a b hab
  have hr : Fin.append a.val.2 (Q.toFun a) = Fin.append b.val.2 (Q.toFun b) := congrArg Prod.snd hab
  have hctx : SameCoordinateContext i a.val b.val := by
    refine ⟨?_,?_⟩
    · intro j hj
      have h := congrArg (fun q : Point (M := M) n (m+d) => q.1 j) hab
      simpa only [codedCoordinateUpdate,replace,Function.update_of_ne hj,GammaRVMap.attachment] using h
    · funext j
      simpa only [Fin.append_left] using congrFun hr (Fin.castAdd d j)
  have hQ : Q.toFun a = Q.toFun b := by
    funext j
    simpa only [Fin.append_right] using congrFun hr (Fin.natAdd m j)
  apply hinj a b hctx hQ
  have h := congrArg (fun q : Point (M := M) n (m+d) => q.1 i) hab
  simpa only [codedCoordinateUpdate,replace,Function.update_self] using h

theorem coded_coordinate_unary_factorization (Q : GammaRVMap G A d) (i : Fin n) (g : A → VF (M := M))
    (hg : GammaScalarGraphDefinable G (fun p y => ∃ a : A, a.val = p ∧ g a = y))
    (hinj : ∀ a b : A, SameCoordinateContext i a.val b.val →
      Q.toFun a = Q.toFun b → g a = g b → a = b) :
    ∃ C : Set (Point (M := M) n (m+d)), ∃ T : GammaUnaryChain G n A C,
      ∀ a : A, (T.toIso.equiv a).val = codedCoordinateUpdate Q i g a := by
  let e := RVAttachment.gammaIso Q
  let E := RVAttachment.target Q
  let g' : E → VF (M := M) := fun b => g (e.equiv.symm b)
  have hg' : GammaScalarGraphDefinable G (fun p y => ∃ b : E, b.val = p ∧ g' b = y) :=
    gamma_iso_precomp_scalar (e.symm (gammaLogicInput G)) g hg
  have hinj' : Function.Injective (fun b : E => replace i b.val (g' b)) := by
    intro b c heq
    have hb : Q.attachment (e.equiv.symm b) = b.val := congrArg Subtype.val (e.equiv.apply_symm_apply b)
    have hc : Q.attachment (e.equiv.symm c) = c.val := congrArg Subtype.val (e.equiv.apply_symm_apply c)
    have h : codedCoordinateUpdate Q i g (e.equiv.symm b) = codedCoordinateUpdate Q i g (e.equiv.symm c) := by
      change replace i (Q.attachment _) _ = replace i (Q.attachment _) _
      rw [hb,hc]
      exact heq
    exact e.equiv.symm.injective (codedCoordinateUpdate_injective Q i g hinj h)
  let u := scalarUpdateIso (G := G) i g' hg' hinj'
  refine ⟨scalarUpdateTarget i g',.cons i e (fun a j _ => rfl)
    (.cons i u (scalarUpdateIso_unary i g' hg' hinj')
      (.nil _ (u.target_definable (gammaLogicInput G)))),?_⟩
  intro a
  change replace i (Q.attachment a) (g (e.equiv.symm (e.equiv a))) = _
  rw [e.equiv.symm_apply_apply]
  rfl

end IntegrationInACVF.Section5
