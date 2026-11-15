import IntegrationSection6.GammaSortedParameterPreservation
import IntegrationSection6.GammaRVGraphRaw

/-! Actual sorted-tuple isomorphisms on pure RV domains return to the
inherited point language without changing a label or a parameter. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {a b : ℕ}

def pureRVSortedPointEquiv (D : Set (Fin a → M))
    (hD : ∀ r ∈ D, ∀ j, iRV (r j)) :
    {q : Point (M := M) 0 a | rvValues q.2 ∈ D} ≃ D where
  toFun q := ⟨rvValues q.val.2,q.property⟩
  invFun r := ⟨(Fin.elim0,fun j => ⟨r.val j,hD r.val r.property j⟩),r.property⟩
  left_inv q := by
    apply Subtype.ext
    exact Prod.ext (Subsingleton.elim _ _) rfl
  right_inv r := rfl

def pureRVSortedPointIso {D : Set (Fin a → M)} {E : Set (Fin b → M)}
    (e : GammaSortedIso B (fun _ => .rv) (fun _ => .rv) D E)
    (hD : ∀ r ∈ D, ∀ j, iRV (r j)) (hE : ∀ r ∈ E, ∀ j, iRV (r j)) :
    GammaIso B {q : Point (M := M) 0 a | rvValues q.2 ∈ D}
      {q : Point (M := M) 0 b | rvValues q.2 ∈ E} := by
  let P := pureRVSortedPointEquiv D hD
  let Q := pureRVSortedPointEquiv E hE
  let f := P.trans (e.equiv.trans Q.symm)
  have hsort : Fin.append (fun _ : Fin a => SortTag.rv) (fun _ : Fin b => .rv) = (fun _ => .rv) := by
    funext j
    refine Fin.addCases (fun _ => ?_) (fun _ => ?_) j <;> simp only [Fin.append_left,Fin.append_right]
  have hGraph := gamma_rv_graph_from_tuple_formula (hsort ▸ e.graph)
  refine ⟨f,?_⟩
  apply GammaGraphDefinable.congr hGraph
  intro p q
  change (∃ u : D, Fin.append u.val (e.equiv u).val = Fin.append (rvValues p.2) (rvValues q.2)) ↔ _
  rw [e.graph_iff]
  constructor
  · rintro ⟨u,hu,hv⟩
    let x := P.symm u
    have hx : x.val = p := pureRVPoint_raw_injective hu
    have hy : (f x).val = q := by
      apply pureRVPoint_raw_injective
      change (e.equiv (P (P.symm u))).val = rvValues q.2
      rw [Equiv.apply_symm_apply]
      exact hv
    exact ⟨x,hx,hy⟩
  · rintro ⟨x,hx,hy⟩
    exact ⟨P x,congrArg (fun z : Point (M := M) 0 a => rvValues z.2) hx,
      congrArg (fun z : Point (M := M) 0 b => rvValues z.2) hy⟩

theorem pure_rv_sorted_point_iso_values {D : Set (Fin a → M)} {E : Set (Fin b → M)}
    (e : GammaSortedIso B (fun _ => .rv) (fun _ => .rv) D E)
    (hD : ∀ r ∈ D, ∀ j, iRV (r j)) (hE : ∀ r ∈ E, ∀ j, iRV (r j))
    (q : {q : Point (M := M) 0 a | rvValues q.2 ∈ D}) :
    rvValues ((pureRVSortedPointIso e hD hE).equiv q).val.2 =
      (e.equiv ((pureRVSortedPointEquiv D hD) q)).val := rfl

end IntegrationInACVF.Section7
