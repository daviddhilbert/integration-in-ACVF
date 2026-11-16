module

public import Integration7.HKMixedFibreConstraintRows
public import Integration7.HKPointIsomorphismCodes

@[expose] public section

/-! Pointwise isomorphisms satisfying an actual mixed graph relation
uniformize to one original-base chart inside that same relation. -/
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

theorem mixed_fibre_row_constrained_chart
    (U : Set (Point (M := M) p a)) (V : Set (Point (M := M) p b))
    (R : Point (M := M) p a → Point (M := M) p b → Prop) (hR : GammaGraphDefinable B R)
    (x : Point (M := M) p 0)
    (f : GammaIso ⟨B.real ∪ Set.range (rawVFParameter x),B.gamma⟩
      (vfParameterFibre (p := p) (n := 0) U x.1) (vfParameterFibre (p := p) (n := 0) V x.1))
    (hf : ∀ u : vfParameterFibre (p := p) (n := 0) U x.1,
      R (Fin.append x.1 u.val.1,u.val.2) (Fin.append x.1 (f.equiv u).val.1,(f.equiv u).val.2)) :
    ∃ C : GammaSortedBijectionChart B (fun _ : Fin p => .vf) (gammaPointSort 0 a) (gammaPointSort 0 b),
      C.carrier ⊆ mixedFibreConstraint R ∧
        C.valid (mixedVFParameterDomain (p := p) (n := 0) U)
          (mixedVFParameterDomain (p := p) (n := 0) V) (rawVFParameter x) := by
  let hDU := mixedVFParameterDomain_row (p := p) (n := 0) U x.1
  let hEV := mixedVFParameterDomain_row (p := p) (n := 0) V x.1
  let g := (GammaIso.toSortedIso f).congr hDU.symm hEV.symm
  apply promote_row_bijection_within (sp := fun _ : Fin p => .vf)
    (rawVFParameter x)
    (fun j => (x.1 j).property) (mixedFibreConstraint R) (mixed_fibre_constraint_definable hR) g
  intro w
  obtain ⟨u,hu,hwu⟩ := (Set.ext_iff.mp hDU w.val).mp w.property
  let u₀ : vfParameterFibre (p := p) (n := 0) U x.1 := ⟨u,hu⟩
  let c : gammaPointCode '' vfParameterFibre (p := p) (n := 0) U x.1 :=
    ⟨w.val,(Set.ext_iff.mp hDU w.val).mp w.property⟩
  have hc : c = pointSetCodeEquiv _ u₀ := Subtype.ext hwu.symm
  have hy : (g.equiv w).val = gammaPointCode (f.equiv u₀).val := by
    calc
      (g.equiv w).val = ((GammaIso.toSortedIso f).equiv c).val :=
        sorted_iso_congr_value (GammaIso.toSortedIso f) hDU.symm hEV.symm w
      _ = gammaPointCode (f.equiv u₀).val := by
        rw [hc]
        exact point_iso_sorted_code f u₀
  have hm := (mixed_fibre_constraint_pack R x.1 u (f.equiv u₀).val).mpr (hf u₀)
  let pair := fun (r : Fin (0+a) → M) (s : Fin (0+b) → M) =>
    Fin.append (Fin.append (rawVFParameter x) r) s
  have he : pair w.val (g.equiv w).val = pair (gammaPointCode u) (gammaPointCode (f.equiv u₀).val) :=
    congrArg₂ pair hwu.symm hy
  change pair w.val (g.equiv w).val ∈ mixedFibreConstraint R
  rw [he]
  exact hm


theorem mixed_fibre_constrained_chart {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
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
    ∃ C : GammaSortedBijectionChart B (fun _ : Fin p => .vf) (gammaPointSort 0 a) (gammaPointSort 0 b),
      C.carrier ⊆ mixedFibreConstraint R ∧ ∀ z ∈ rawVFParameter '' A,
        C.valid (mixedVFParameterDomain (p := p) (n := 0) U)
          (mixedVFParameterDomain (p := p) (n := 0) V) z := by
  have hD := gamma_mixedVFParameterDomain (p := p) (n := 0) U hU
  have hE := gamma_mixedVFParameterDomain (p := p) (n := 0) V hV
  have hPA := gamma_raw_vf_parameter_base hA
  apply uniform_bijection_chart_within hκ hs hr hg _ hPA hD hE (mixedFibreConstraint R)
  rintro z ⟨x,hx,rfl⟩
  obtain ⟨f,hf⟩ := hrow ⟨x,hx⟩
  exact mixed_fibre_row_constrained_chart U V R hR x f hf

end IntegrationInACVF.Section7.HK
