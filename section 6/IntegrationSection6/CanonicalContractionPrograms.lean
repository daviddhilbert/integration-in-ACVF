import IntegrationSection6.StandardProgramPresentations
import IntegrationSection5.NaturalContractionGamma

/-! RV-pullbacks have actual contraction programs with identity head
preparations. Their natural maps fix VF and their RV maps are contractible. -/
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
open IntegrationInACVF.Section5
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {S : Set M} {n a : ℕ}

theorem headKey_contractible {p q : Point (M := M) (n+1) a} (h : SameRV p q) :
    SameRV (headKey p) (headKey q) := by
  obtain ⟨hVF,hRV⟩ := (sameRV_iff p q).mp h
  apply (sameRV_iff _ _).mpr
  refine ⟨fun j => hVF j.succ,?_⟩
  change Fin.append (fun _ : Fin 1 => @rv M sM hM (vfAt p 0)) p.2 =
    Fin.append (fun _ : Fin 1 => @rv M sM hM (vfAt q 0)) q.2
  exact congrArg₂ Fin.append (funext fun _ => hVF 0) hRV

theorem canonical_ordered_contraction_exists :
    ∀ {n a : ℕ} (U : DefSet (M := M) S n a)
      (hU : GammaSetDefinable B (carrier U)) (hPull : IsRVPullback (carrier U)),
    ∃ l : ℕ, ∃ V : DefSet (M := M) S 0 l, ∃ T : OrderedContractionProgram S U V,
      GammaProgramDefinable B T ∧ (∀ u : U, (T.naturalMap u).val.1 = u.val.1) ∧ Contractible T.toMap := by
  intro n
  induction n with
  | zero =>
    intro a U hU hPull
    exact ⟨a,U,.zero U,hU,fun _ => rfl,fun _ _ h => h⟩
  | succ n ih =>
    intro a U hU hPull
    let H : HeadPreparation U := ⟨a,U,Map.id U,specialRelative_id U 0,headSaturated_of_pullback hPull⟩
    obtain ⟨l,V,T,hT,hVF,hc⟩ := ih H.contractedSet (gamma_headImage U hU) (headImage_pullback U hPull)
    refine ⟨l,V,.step H T,⟨gamma_identity_graph U hU,hU,hT⟩,?_,?_⟩
    · intro u
      funext j
      cases j using Fin.cases with
      | zero => rfl
      | succ j => exact congrFun (hVF (H.contractionMap u)) j
    · intro u v huv
      apply hc
      change SameRV (headKeyMap U u).val (headKeyMap U v).val
      rw [headKeyMap_apply,headKeyMap_apply]
      exact headKey_contractible huv

theorem canonical_standard_contraction_exists (U : DefSet (M := M) S n a)
    (hU : GammaSetDefinable B (carrier U)) (hPull : IsRVPullback (carrier U)) :
    ∃ C : StandardContraction U (Equiv.refl _), GammaProgramDefinable B C.program ∧
      (∀ u : U, (C.naturalMap u).val.1 = u.val.1) ∧ Contractible C.toMap := by
  have hEq := vfPermutationImage_id_eq U
  obtain ⟨l,V,T,hT,hVF,hc⟩ := canonical_ordered_contraction_exists (vfPermutationImage U (Equiv.refl _))
    (gamma_vfPermutationImage U hU _) (hEq.symm ▸ hPull)
  let C : StandardContraction U (Equiv.refl _) := ⟨l,V,T⟩
  refine ⟨C,hT,?_,?_⟩
  · intro u
    exact hVF (vfPermutationBijection U (Equiv.refl _) u)
  · intro u v huv
    exact hc (vfPermutationBijection U (Equiv.refl _) u) (vfPermutationBijection U (Equiv.refl _) v) huv

end IntegrationInACVF.Section6
