import IntegrationSection5.FiniteHeadPreparation
import IntegrationSection5.GammaHeadPreparation
import Section5.GammaLiftRelation

/-! A uniform original-Gamma RV code separates every finite head fibre.
Only smallness of the original real base is used, irrespective of the
working real presentation of the family. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5 SpecialTransformations.Section3
namespace IntegrationInACVF.Section5
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {S : Set M} {n m : ℕ}

theorem finite_head_family_rv_encoding {κ : Cardinal} (hs : Saturated M κ)
    (h00 : M ⊨ Axioms.ACVF00) (P : GammaParameters.Base (M := M))
    (hsmall : Cardinal.mk P.real < κ) (F : VFFieldBase P.real) (hPS : P.real ⊆ S)
    (A : DefSet (M := M) S (n+1) m) (hA : GammaSetDefinable P (carrier A))
    (hfinite : HeadPreparation.FiniteHeadFibres A) :
    ∃ l, ∃ f : Map A (PresentedSet.univ (pointSpace 0 l) S),
      GammaGraphDefinable P (pointMapGraph f) ∧
      ∀ a b : A, TailEq a.val b.val → f a = f b → a = b := by
  obtain ⟨T,_,_,_,hT⟩ := gamma_head_preparation hs h00 P hsmall F hPS A hA
  let f := postcomposeRealMap T.map (pointLabels P.real (n+1) T.arity) hPS
  refine ⟨T.arity,f,gamma_postcompose_real (gammaLogicInput P) T.map hT _ hPS,?_⟩
  intro a b ht hf
  apply T.finite_fibres_labels_separate hfinite a b ht
  have h := congrArg (fun z : PresentedSet.univ (pointSpace (M := M) 0 T.arity) S => z.val.2) hf
  have ha := pointLabels_snd P.real (n+1) T.arity ⟨(T.map a).val,Set.mem_univ _⟩
  have hb := pointLabels_snd P.real (n+1) T.arity ⟨(T.map b).val,Set.mem_univ _⟩
  exact ha.symm.trans (h.trans hb)

end IntegrationInACVF.Section5
