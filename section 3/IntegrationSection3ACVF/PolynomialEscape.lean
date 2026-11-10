import Section3.PolynomialRVConstant
import Section3.ClosedBallRoots

/-! Finite-polynomial closed-ball escape, the geometric content
used in the paper's Lemma 2.12 and later in 3.14. Reuses the pinned proved
root-free enlargement and polynomial RV factorization declarations. -/

set_option backward.isDefEq.respectTransparency false

open Set Classical FirstOrder FirstOrder.Language ValOneEC
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3

namespace IntegrationInACVF.Section3ACVF.PolynomialEscape

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {Γ : Type} [LinearOrderedCommGroupWithZero Γ]

theorem outside_closed (v : Valuation (VFType (M := M)) Γ)
    (hnt : ∃ x : VFType (M := M), x ≠ 0 ∧ v x < 1) (a r : VFType (M := M)) :
    ∃ x : VFType (M := M), ¬ v (x-a) ≤ v r := by
  let : IsAlgClosed (VFType (M := M)) := VFAlgClosed.isAlgClosed_vfType
  obtain ⟨z,_,hrz,_⟩ := Johnson.exists_val_gt_max v hnt r r
  refine ⟨a+z,?_⟩
  simpa only [add_sub_cancel_left] using not_le_of_gt hrz

theorem finite_polynomial_escape (v : Valuation (VFType (M := M)) Γ)
    (hv : ∀ x y : VFType (M := M), VFValued.predV x y ↔ v x ≤ v y)
    (hnt : ∃ x : VFType (M := M), x ≠ 0 ∧ v x < 1)
    (F : Finset (Polynomial (VFType (M := M)))) (a r : VFType (M := M))
    (hroots : ∀ p ∈ F, ∀ c ∈ p.roots, ¬ v (c-a) ≤ v r) :
    ∃ x : VFType (M := M), ¬ v (x-a) ≤ v r ∧
      ∀ p ∈ F, iRv (p.eval x).val = iRv (p.eval a).val := by
  classical
  let R := F.biUnion (fun p => p.roots.toFinset)
  have hrootmem (p : Polynomial (VFType (M := M))) (hp : p ∈ F)
      (c : VFType (M := M)) (hc : c ∈ p.roots) : c ∈ R :=
    Finset.mem_biUnion.mpr ⟨p,hp,Multiset.mem_toFinset.mpr hc⟩
  by_cases hR : R.Nonempty
  · have hmiss (c : VFType (M := M)) (hc : c ∈ R) : ¬ v (c-a) ≤ v r := by
      obtain ⟨p,hp,hcp⟩ := Finset.mem_biUnion.mp hc
      exact hroots p hp c (Multiset.mem_toFinset.mp hcp)
    let : IsAlgClosed (VFType (M := M)) := VFAlgClosed.isAlgClosed_vfType
    obtain ⟨d,hproper,havoid⟩ := ClosedBallRoots.enlarge v hnt R hR a r hmiss
    obtain ⟨x,hx,hxout⟩ := Set.not_subset.mp hproper.2
    have ha : a ∈ ValOneEC.openBall v a (v d) :=
      hproper.1 (by simpa only [ValOneEC.closedBall,Set.mem_ofPred_eq,sub_self,map_zero] using
        (zero_le : (0 : Γ) ≤ v r))
    have hd0 : v d ≠ 0 := ne_of_gt (by
      simpa only [ValOneEC.openBall,Set.mem_ofPred_eq,sub_self,map_zero] using ha)
    have hopen : Balls.openDisc v a (↑(OrderDual.toDual (v d)) : Balls.Radius Γ) =
        ValOneEC.openBall v a (v d) := by
      simp [Balls.openDisc,hd0,ValOneEC.openBall]
    refine ⟨x,hxout,?_⟩
    intro p hp
    apply polynomial_rv_constant_openDisc v hv p a
      (↑(OrderDual.toDual (v d)) : Balls.Radius Γ)
    · intro c hc
      rw [hopen]
      exact havoid c (hrootmem p hp c hc)
    · rwa [hopen]
    · rwa [hopen]
  · obtain ⟨x,hx⟩ := outside_closed v hnt a r
    refine ⟨x,hx,?_⟩
    intro p hp
    apply polynomial_rv_eq_of_linear_factors p x a
    intro c hc
    exact (hR ⟨c,hrootmem p hp c hc⟩).elim

theorem same_rv_escape (v : Valuation (VFType (M := M)) Γ)
    (hv : ∀ x y : VFType (M := M), VFValued.predV x y ↔ v x ≤ v y)
    (hnt : ∃ x : VFType (M := M), x ≠ 0 ∧ v x < 1)
    (F : Finset (Polynomial (VFType (M := M)))) (a r : VFType (M := M))
    (hzero : ¬ v ((0 : VFType (M := M))-a) ≤ v r)
    (hroots : ∀ p ∈ F, ∀ c ∈ p.roots, ¬ v (c-a) ≤ v r) :
    ∃ x : VFType (M := M), ¬ v (x-a) ≤ v r ∧ iRv x.val = iRv a.val ∧
      ∀ p ∈ F, iRv (p.eval x).val = iRv (p.eval a).val := by
  classical
  have hG : ∀ p ∈ insert Polynomial.X F, ∀ c ∈ p.roots, ¬ v (c-a) ≤ v r := by
    intro p hp c hc
    rcases Finset.mem_insert.mp hp with hp | hp
    · subst p
      have hc0 : c = 0 := by
        simpa only [Polynomial.roots_X,Multiset.mem_singleton] using hc
      simpa only [hc0] using hzero
    · exact hroots p hp c hc
  obtain ⟨x,hx,he⟩ := finite_polynomial_escape v hv hnt (insert Polynomial.X F) a r hG
  refine ⟨x,hx,?_,fun p hp => he p (Finset.mem_insert_of_mem hp)⟩
  simpa only [Polynomial.eval_X] using he Polynomial.X (Finset.mem_insert_self _ _)

/-- Closed-ball alternative of 2.12 with a nondegenerate prescribed
ambient RV fibre. The polynomial list may include zero polynomials. -/
theorem closed_escape_in_rv_fibre (v : Valuation (VFType (M := M)) Γ)
    (hv : ∀ x y : VFType (M := M), VFValued.predV x y ↔ v x ≤ v y)
    (hnt : ∃ x : VFType (M := M), x ≠ 0 ∧ v x < 1)
    (F : Finset (Polynomial (VFType (M := M)))) (a r : VFType (M := M))
    (t : CanonicalRV.RVSort M) (ht0 : t.val ≠ iRVZero)
    (hsub : ∀ x : VFType (M := M), v (x-a) ≤ v r → CanonicalRV.encodedRv x = t)
    (hroots : ∀ p ∈ F, ∀ c ∈ p.roots, ¬ v (c-a) ≤ v r) :
    ∃ x : VFType (M := M), ¬ v (x-a) ≤ v r ∧ CanonicalRV.encodedRv x = t ∧
      ∀ p ∈ F, iRv (p.eval x).val = iRv (p.eval a).val := by
  have hzero : ¬ v ((0 : VFType (M := M))-a) ≤ v r := by
    intro hz
    have he := congrArg Subtype.val (hsub 0 hz).symm
    exact ht0 (he.trans ((CanonicalRV.encodedRv_zero_iff (0 : VFType (M := M))).mpr rfl))
  obtain ⟨x,hx,hsame,hpolys⟩ := same_rv_escape v hv hnt F a r hzero hroots
  have ha : v (a-a) ≤ v r := by
    simpa only [sub_self,map_zero] using (zero_le : (0 : Γ) ≤ v r)
  have hxa : CanonicalRV.encodedRv x = CanonicalRV.encodedRv a := Subtype.ext hsame
  exact ⟨x,hx,hxa.trans (hsub a ha),hpolys⟩

end IntegrationInACVF.Section3ACVF.PolynomialEscape
