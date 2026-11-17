module

public import Integration7.GammaRectangleFamilyHeadPreparations
public import Integration7.UnarySpecialHeadPreparations
public import IntegrationSection6.StandardProgramPresentations

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Actual original-Gamma standard contractions of a shared-label
rectangle family in both VF coordinate orders. The head preparations
come from the actual labelled unary projections. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5
open IntegrationInACVF.Section4 IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {G : Base (M := M)} {S : Set M} {m : ℕ}

theorem rectangular_rv_fibres_of_mix (H : Set (Point (M := M) 2 m))
    (hMix : ∀ p q : H, p.val.2=q.val.2 → (![vfAt p.val 0,vfAt q.val 1],p.val.2) ∈ H) :
    RectangularRVFibres H := by
  intro r
  apply (relation_eq_projection_product_iff _).mpr
  intro p hp q hq
  exact hMix ⟨((pairPoint q.1 q.2).1,r),hq⟩ ⟨((pairPoint p.1 p.2).1,r),hp⟩ rfl

theorem rectangular_rv_fibres_swap (H : DefSet (M := M) S 2 m) (hH : RectangularRVFibres (carrier H)) :
    RectangularRVFibres (carrier (vfPermutationImage H (Equiv.swap 0 1))) := by
  apply rectangular_rv_fibres_of_mix
  intro p q hRV
  obtain ⟨p₀,hp₀⟩ := p.property
  obtain ⟨q₀,hq₀⟩ := q.property
  have hRV₀ := (congrArg (fun z : Point (M := M) 2 m => z.2) hp₀).trans
    (hRV.trans (congrArg (fun z : Point (M := M) 2 m => z.2) hq₀).symm)
  have hMix := rectangular_rv_fibres_mix hH q₀ p₀ hRV₀.symm
  have hpHead := congrArg (fun z : Point (M := M) 2 m => vfAt z 0) hp₀
  have hqTail := congrArg (fun z : Point (M := M) 2 m => vfAt z 1) hq₀
  refine ⟨⟨(![vfAt q₀.val 0,vfAt p₀.val 1],q₀.val.2),hMix⟩,?_⟩
  apply Prod.ext
  · funext i
    fin_cases i
    · exact hpHead
    · exact hqTail
  · exact (congrArg (fun z : Point (M := M) 2 m => z.2) hq₀).trans hRV.symm

theorem rectangle_family_standard_contraction_exists (C : BaseContext M)
    (hNames : commonRealNames G ⊆ (C.base : Set M))
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ G.gamma) (hγ1 : 1 < γ)
    (H : DefSet (M := M) (C.base : Set M) 2 m) (hH : GammaSetDefinable G (carrier H))
    (hRect : RectangularRVFibres (carrier H)) :
    ∃ E : StandardContraction H (Equiv.refl _), GammaProgramDefinable G E.program := by
  obtain ⟨P,hP,hY⟩ := gamma_rectangle_family_head_preparation_exists C hNames γ hγ hγ1 H hH hRect
  obtain ⟨r,D,T,hT,hD⟩ := gamma_unary_pullback_preparation_over_common_names C hNames γ hγ hγ1
    P.contractedSet (gamma_headImage P.target hY)
  let W := OrderedContractionProgram.step P (unarySpecialContractionProgram T hD)
  have hW : GammaProgramDefinable G W := ⟨hP,hY,gamma_unary_special_contraction_program T hD hT⟩
  exact ⟨standardFromProgram H (Equiv.refl _) W (vfPermutationImage_id_eq H).symm,
    gamma_standardFromProgram H _ W _ hW⟩

theorem rectangle_family_swapped_standard_contraction_exists (C : BaseContext M)
    (hNames : commonRealNames G ⊆ (C.base : Set M))
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ G.gamma) (hγ1 : 1 < γ)
    (H : DefSet (M := M) (C.base : Set M) 2 m) (hH : GammaSetDefinable G (carrier H))
    (hRect : RectangularRVFibres (carrier H)) :
    ∃ E : StandardContraction H (Equiv.swap 0 1), GammaProgramDefinable G E.program := by
  let X := vfPermutationImage H (Equiv.swap 0 1)
  obtain ⟨T,hT⟩ := rectangle_family_standard_contraction_exists C hNames γ hγ hγ1 X
    (gamma_vfPermutationImage H hH (Equiv.swap 0 1)) (rectangular_rv_fibres_swap H hRect)
  exact ⟨standardFromProgram H (Equiv.swap 0 1) T.program (vfPermutationImage_id_eq X),
    gamma_standardFromProgram H _ T.program _ hT⟩

end IntegrationInACVF.Section7
