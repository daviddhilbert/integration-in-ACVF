module

public import Integration7.HKGenericConstrainedCharts
public import Integration7.HKMixedFibreConstraintRealization
public import Integration7.HKPureVFGammaLoci

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Exact mixed relations on generic weighted rows produce one actual
original-base isomorphism on a definable locus containing all generic VF
tuples. The isomorphism preserves every VF coordinate and the relation. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7.HK
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p a b : ℕ}

theorem generic_mixed_fibre_constrained {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (hr : Cardinal.mk B.real < κ) (hg : Cardinal.mk B.gamma < κ)
    (U : Set (Point (M := M) p a)) (V : Set (Point (M := M) p b))
    (hU : GammaSetDefinable B U) (hV : GammaSetDefinable B V)
    (R : Point (M := M) p a → Point (M := M) p b → Prop) (hR : GammaGraphDefinable B R)
    (hrow : ∀ x : Fin p → VFType (M := M), AlgebraicIndependent (vfParameterField B.real) x →
      ∃ e : GammaIso ⟨B.real ∪ Set.range (vfValues x),B.gamma⟩
        (vfParameterFibre (p := p) (n := 0) U x) (vfParameterFibre (p := p) (n := 0) V x),
        ∀ u : vfParameterFibre (p := p) (n := 0) U x,
          R (Fin.append x u.val.1,u.val.2) (Fin.append x (e.equiv u).val.1,(e.equiv u).val.2)) :
    ∃ A : Set (Point (M := M) p 0), GammaSetDefinable B A ∧
      (∀ x : Fin p → VFType (M := M), AlgebraicIndependent (vfParameterField B.real) x → (x,Fin.elim0) ∈ A) ∧
      ∃ e : GammaIso B {q | (q.1,Fin.elim0) ∈ A ∧ q ∈ U} {q | (q.1,Fin.elim0) ∈ A ∧ q ∈ V},
        VFParametersPreserved (p := p) (n := 0) (m := 0) e ∧ ∀ u, R u.val (e.equiv u).val := by
  have hD := gamma_mixedVFParameterDomain (p := p) (n := 0) U hU
  have hE := gamma_mixedVFParameterDomain (p := p) (n := 0) V hV
  obtain ⟨C,hCK,hC⟩ := generic_bijection_chart_within hκ hs hr hg hD hE (mixedFibreConstraint R) (by
    intro x hx
    obtain ⟨e,he⟩ := hrow x hx
    exact mixed_fibre_row_constrained_chart U V R hR (x,Fin.elim0) e he)
  let A : Set (Point (M := M) p 0) :=
    {q | C.valid (mixedVFParameterDomain (p := p) (n := 0) U)
      (mixedVFParameterDomain (p := p) (n := 0) V) (vfValues q.1)}
  have hA : GammaSetDefinable B A := gamma_pure_vf_locus (C.valid_definable hD hE)
  refine ⟨A,hA,hC,?_⟩
  exact mixed_fibre_chart_realization A hA U V hU hV R C hCK (by
    rintro z ⟨x,hx,rfl⟩
    exact hx)

end IntegrationInACVF.Section7.HK
