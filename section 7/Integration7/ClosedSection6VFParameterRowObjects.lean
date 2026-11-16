module

public import Integration7.CompletedSection6Kernel
public import Integration7.ClosedSection6GammaVFAllFinitePresentation
public import IntegrationSection6.VFParameterRowObjects
public import IntegrationSection6.MixedVFParameterDomains
public import IntegrationSection6.VFParameterCoefficientBases
public import IntegrationSection6.GammaVFAllFinitePresentation

@[expose] public section

/-! Closed generated-base Section6 integration. The former universal
Section5 input is replaced by the canonical-model certificate; its kernel
uses the proved generated-base contraction comparison. Original finite
objects, actual lifting, scissor addition and Cartesian products are retained.
This module keeps the dependent data and consumers in one coherent interface. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section6 IntegrationInACVF.Section6.FiniteRV
namespace IntegrationInACVF.Section7.CompletedSection6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p n a : ℕ}

theorem gamma_vfParameterFibre (U : Set (Point (M := M) (p+n) a)) (hU : GammaSetDefinable B U)
    (x : Fin p → VF (M := M)) :
    GammaSetDefinable ⟨B.real ∪ Set.range (fun j => (x j).val),B.gamma⟩ (vfParameterFibre U x) := by
  have hD := gamma_mixedVFParameterDomain (p := p) (n := n) U hU
  have h := gamma_tuple_parameter_specialize (fun _ : Fin p => .vf) (gammaPointSort n a)
    (fun j => (x j).val) hD
  rw [mixedVFParameterDomain_row] at h
  exact h

def vfParameterRowObject (U : Set (Point (M := M) (p+n) a)) (hU : GammaSetDefinable B U)
    (hfin : ∀ z : Fin (p+n) → VF (M := M), {r : Fin a → RV (M := M) | (z,r) ∈ U}.Finite)
    (x : Fin p → VF (M := M)) : IntegrationInACVF.Section7.CompletedSection6.GammaVFAllFiniteObject (vfParameterCoefficientBase B x) where
  arity := (n,a)
  domain := vfParameterFibre U x
  definable := (gamma_vfParameterFibre U hU x).mono
    (subset_closureBase (⟨B.real ∪ Set.range (fun j => (x j).val),B.gamma⟩ : Base (M := M))).1
    (subset_closureBase (⟨B.real ∪ Set.range (fun j => (x j).val),B.gamma⟩ : Base (M := M))).2
  finiteFibres := fun z => hfin (Fin.append x z)

end IntegrationInACVF.Section7.CompletedSection6
