module

public import Integration7.HKMixedFibreConstraintPromotion
public import IntegrationSection6.GammaMixedParameterUniformity

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Realization of the constrained compactness chart preserves the actual
point relation, as well as every VF parameter. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7.HK
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p a b : ℕ}

theorem relation_of_sorted_fibre_constraint
    (R : Point (M := M) p a → Point (M := M) p b → Prop)
    (u : Point (M := M) p a) (v : Point (M := M) p b)
    (r : Fin (p+(0+a)) → M) (s : Fin (p+(0+b)) → M)
    (hu : gammaPointCode u = r ∘ finCongr (Nat.add_assoc p 0 a))
    (hv : gammaPointCode v = s ∘ finCongr (Nat.add_assoc p 0 b))
    (hp : s ∘ Fin.castAdd (0+b) = r ∘ Fin.castAdd (0+a))
    (hK : Fin.append r (s ∘ Fin.natAdd p) ∈ mixedFibreConstraint R) : R u v := by
  let ρ := finCongr (Nat.add_assoc p 0 a)
  let τ := finCongr (Nat.add_assoc p 0 b)
  have hc : Fin.append r (s ∘ Fin.natAdd p) ∘ mixedFibreConstraintCoordinates p a b =
      Fin.append (gammaPointCode u) (gammaPointCode v) := by
    exact (congrArg (fun f => f ∘ sortedPairCoordinates ρ τ)
      (repeat_coordinates_of_common_prefix r s hp)).trans
      ((append_sortedPairCoordinates ρ τ r s).trans (congrArg₂ Fin.append hu.symm hv.symm))
  exact (point_relation_codes_iff R u v).mp (hc ▸ hK.1)

theorem mixed_fibre_chart_realization
    (A : Set (Point (M := M) p 0)) (hA : GammaSetDefinable B A)
    (U : Set (Point (M := M) p a)) (V : Set (Point (M := M) p b))
    (hU : GammaSetDefinable B U) (hV : GammaSetDefinable B V)
    (R : Point (M := M) p a → Point (M := M) p b → Prop)
    (C : GammaSortedBijectionChart B (fun _ : Fin p => .vf) (gammaPointSort 0 a) (gammaPointSort 0 b))
    (hCK : C.carrier ⊆ mixedFibreConstraint R)
    (hC : ∀ z ∈ rawVFParameter '' A, C.valid
      (mixedVFParameterDomain (p := p) (n := 0) U) (mixedVFParameterDomain (p := p) (n := 0) V) z) :
    ∃ e : GammaIso B {q | (q.1,Fin.elim0) ∈ A ∧ q ∈ U}
      {q | (q.1,Fin.elim0) ∈ A ∧ q ∈ V},
      VFParametersPreserved (p := p) (n := 0) (m := 0) e ∧ ∀ u, R u.val (e.equiv u).val := by
  have hD := gamma_mixedVFParameterDomain (p := p) (n := 0) U hU
  have hE := gamma_mixedVFParameterDomain (p := p) (n := 0) V hV
  let e := gammaSortedTotalIso C (gamma_raw_vf_parameter_base hA) hE hC
  have he := gammaSortedTotalEquiv_prefix C hE hC
  let ρ := finCongr (Nat.add_assoc p 0 a)
  let τ := finCongr (Nat.add_assoc p 0 b)
  let f := e.toPointIso ρ τ mixedVFParameterSort_cast mixedVFParameterSort_cast
    (fun z hz => hD.proper z hz.2) (fun z hz => hE.proper z hz.2)
  have hf : VFParametersPreserved (p := p) (n := 0) (m := 0) f := by
    intro u j
    let ru := (⟨gammaPointCode u.val ∘ ρ.symm,u.property⟩ :
      rawRowTotal (rawVFParameter '' A) (mixedVFParameterDomain (p := p) (n := 0) U))
    have hc := gammaSortedIso_toPointIso_code e ρ τ mixedVFParameterSort_cast mixedVFParameterSort_cast
      (fun z hz => hD.proper z hz.2) (fun z hz => hE.proper z hz.2) u
    have ht : gammaPointCode (f.equiv u).val ∘ τ.symm = (e.equiv ru).val := by
      rw [hc]
      funext i
      simp only [Function.comp_apply,Equiv.apply_symm_apply]
      rfl
    have hpref : rawVFParameter ((f.equiv u).val.1 ∘ Fin.castAdd 0,Fin.elim0) =
        rawVFParameter (u.val.1 ∘ Fin.castAdd 0,Fin.elim0) := by
      rw [← mixedVFParameterCode_prefix (f.equiv u).val,← mixedVFParameterCode_prefix u.val]
      change (gammaPointCode (f.equiv u).val ∘ τ.symm) ∘ Fin.castAdd (0+b) =
        (gammaPointCode u.val ∘ ρ.symm) ∘ Fin.castAdd (0+a)
      rw [ht]
      exact he ru
    exact Subtype.ext (congrFun hpref j)
  have hfR : ∀ u, R u.val (f.equiv u).val := by
    intro u
    let ru := (⟨gammaPointCode u.val ∘ ρ.symm,u.property⟩ :
      rawRowTotal (rawVFParameter '' A) (mixedVFParameterDomain (p := p) (n := 0) U))
    apply relation_of_sorted_fibre_constraint R u.val (f.equiv u).val ru.val (e.equiv ru).val
    · funext i
      simp only [Function.comp_apply,Equiv.symm_apply_apply]
      rfl
    · exact gammaSortedIso_toPointIso_code e ρ τ mixedVFParameterSort_cast mixedVFParameterSort_cast
        (fun z hz => hD.proper z hz.2) (fun z hz => hE.proper z hz.2) u
    · exact he ru
    · exact constrained_total_graph C (gamma_raw_vf_parameter_base hA) hE hC
        (mixedFibreConstraint R) hCK ru
  let hU' := mixedVFParameterTotal_points (p := p) (n := 0) A U
  let hV' := mixedVFParameterTotal_points (p := p) (n := 0) A V
  have hU'' : {q | (q.1 ∘ Fin.castAdd 0,Fin.elim0) ∈ A ∧ q ∈ U} =
      {q | (q.1,Fin.elim0) ∈ A ∧ q ∈ U} := by
    ext q
    change ((q.1 ∘ Fin.castAdd 0,Fin.elim0) ∈ A ∧ q ∈ U) ↔ _
    have hz : q.1 ∘ Fin.castAdd 0 = q.1 := funext (fun i => congrArg q.1 (Fin.ext rfl))
    rw [hz]
    rfl
  have hV'' : {q | (q.1 ∘ Fin.castAdd 0,Fin.elim0) ∈ A ∧ q ∈ V} =
      {q | (q.1,Fin.elim0) ∈ A ∧ q ∈ V} := by
    ext q
    change ((q.1 ∘ Fin.castAdd 0,Fin.elim0) ∈ A ∧ q ∈ V) ↔ _
    have hz : q.1 ∘ Fin.castAdd 0 = q.1 := funext (fun i => congrArg q.1 (Fin.ext rfl))
    rw [hz]
    rfl
  let hUF := hU'.trans hU''
  let hVF := hV'.trans hV''
  refine ⟨f.congr hUF hVF,vfParametersPreserved_congr f hf hUF hVF,?_⟩
  intro u
  rw [gammaIsoCongr_value]
  exact hfR ((Equiv.subtypeEquivRight (fun q => Iff.of_eq
    (congrArg (fun S => q ∈ S) hUF))).symm u)


theorem gamma_mixed_fibre_constrained_restricted {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (hr : Cardinal.mk B.real < κ) (hg : Cardinal.mk B.gamma < κ)
    (A : Set (Point (M := M) p 0)) (hA : GammaSetDefinable B A)
    (U : Set (Point (M := M) p a)) (V : Set (Point (M := M) p b))
    (hU : GammaSetDefinable B U) (hV : GammaSetDefinable B V)
    (R : Point (M := M) p a → Point (M := M) p b → Prop) (hR : GammaGraphDefinable B R)
    (hrow : ∀ x : A, ∃ e : GammaIso ⟨B.real ∪ Set.range (rawVFParameter x.val),B.gamma⟩
      (vfParameterFibre (p := p) (n := 0) U x.val.1) (vfParameterFibre (p := p) (n := 0) V x.val.1),
      ∀ u : vfParameterFibre (p := p) (n := 0) U x.val.1,
        R (Fin.append x.val.1 u.val.1,u.val.2)
          (Fin.append x.val.1 (e.equiv u).val.1,(e.equiv u).val.2)) :
    ∃ e : GammaIso B {q | (q.1,Fin.elim0) ∈ A ∧ q ∈ U}
      {q | (q.1,Fin.elim0) ∈ A ∧ q ∈ V},
      VFParametersPreserved (p := p) (n := 0) (m := 0) e ∧ ∀ u, R u.val (e.equiv u).val := by
  obtain ⟨C,hCK,hC⟩ := mixed_fibre_constrained_chart hκ hs hr hg A hA U V hU hV R hR hrow
  exact mixed_fibre_chart_realization A hA U V hU hV R C hCK hC

end IntegrationInACVF.Section7.HK
