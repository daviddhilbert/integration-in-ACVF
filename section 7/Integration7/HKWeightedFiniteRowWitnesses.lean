module

public import Integration7.HKPureRVPointSortedIsomorphisms
public import Integration7.HKPointIsomorphismCodes
public import Integration7.HKDensityLabelConstraints
public import Integration7.GammaFiniteRowIsomorphismWitnesses

@[expose] public section

/-! An exact-density isomorphism of finite zero-volume rows promotes to
a globally density-constrained formula on the original parameter base. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7.HK
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p a b : ℕ} {sp : Fin p → SortTag}

theorem weighted_finite_row_formula_witness
    (F : GammaFiniteRVSchema B p a 0 sp) (G : GammaFiniteRVSchema B p b 0 sp)
    (z : Fin p → M) (hF : F.valid z) (hG : G.valid z)
    (δ : Fin a) (ε : Fin b)
    (e : GammaIso ⟨B.real ∪ Set.range z,B.gamma⟩
      {q : Point (M := M) 0 a | q.2 ∈ F.rowDomain z}
      {q : Point (M := M) 0 b | q.2 ∈ G.rowDomain z})
    (he : ∀ u, u.val.2 δ = (e.equiv u).val.2 ε) :
    ∃ H : GammaRelationFormula B p a b sp,
      H.val ⊆ densityLabelConstraint sp δ ε ∧ (gammaFiniteRowChartSchema F G H).valid z := by
  have hFD : rvValues '' F.rowDomain z = {r | Fin.append z r ∈ F.domain} :=
    Set.ext (fun r => (F.raw_row_domain_iff z r).symm)
  have hGD : rvValues '' G.rowDomain z = {r | Fin.append z r ∈ G.domain} :=
    Set.ext (fun r => (G.raw_row_domain_iff z r).symm)
  let E := (pureRVPointSortedIso e).congr hFD hGD
  have hE : ∀ u, Fin.append (Fin.append z u.val) (E.equiv u).val ∈ densityLabelConstraint sp δ ε := by
    intro u
    let q := (pureRVPointRawEquiv (F.rowDomain z)).symm
      ⟨u.val,(Set.ext_iff.mp hFD u.val).mpr u.property⟩
    have hq : rvValues q.val.2 = u.val := rfl
    have hout : (E.equiv u).val = rvValues (e.equiv q).val.2 := by
      rw [sorted_iso_congr_value]
      have hh := pure_rv_point_sorted_iso_value e q
      have hqu : pureRVPointRawEquiv (F.rowDomain z) q =
          ⟨u.val,(Set.ext_iff.mp hFD u.val).mpr u.property⟩ :=
        (pureRVPointRawEquiv (F.rowDomain z)).apply_symm_apply _
      rw [hqu] at hh
      exact hh
    rw [hout,← hq]
    exact (density_label_constraint_append δ ε z hF.1 q.val.2 (e.equiv q).val.2).mpr (he q)
  obtain ⟨C,hCK,hC⟩ := promote_row_bijection_within z hF.1
    (densityLabelConstraint sp δ ε) (density_label_constraint_definable δ ε) E hE
  refine ⟨⟨C.carrier,C.definable⟩,hCK,hF,hG,hC,?_⟩
  refine ⟨hF.1,?_⟩
  intro r hr hH hV hW
  exact congrArg (fun t : Fin 0 → M => SpecialTransformations.Section7.rawWeight t)
    (Subsingleton.elim _ _)

end IntegrationInACVF.Section7.HK
