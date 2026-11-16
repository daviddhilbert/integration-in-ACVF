import Integration7.PureRVSortedIsomorphisms
import IntegrationSection6.GammaRVGraphRaw

/-! Pure RV point isomorphisms retain their literal label values when
converted to sorted tuples. This also retains an arbitrary exact density. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7.HK
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {a b : ℕ}

def pureRVPointRawEquiv (D : Set (Fin a → CanonicalRV.RVSort M)) :
    {q : Point (M := M) 0 a | q.2 ∈ D} ≃ (rvValues '' D) where
  toFun q := ⟨rvValues q.val.2,⟨q.val.2,q.property,rfl⟩⟩
  invFun r := ⟨(Fin.elim0,fun j => ⟨r.val j,by
    obtain ⟨u,_,hu⟩ := r.property
    exact congrFun hu j ▸ (u j).property⟩),by
      obtain ⟨u,hu,he⟩ := r.property
      have h : (fun j => (⟨r.val j,by exact congrFun he j ▸ (u j).property⟩ : CanonicalRV.RVSort M)) = u := by
        funext j
        exact Subtype.ext (congrFun he j).symm
      exact h.symm ▸ hu⟩
  left_inv q := Subtype.ext (Prod.ext (Subsingleton.elim _ _) rfl)
  right_inv r := rfl

def pureRVPointSortedIso {D : Set (Fin a → CanonicalRV.RVSort M)}
    {E : Set (Fin b → CanonicalRV.RVSort M)}
    (e : GammaIso B {q : Point (M := M) 0 a | q.2 ∈ D}
      {q : Point (M := M) 0 b | q.2 ∈ E}) :
    GammaSortedIso B (fun _ => .rv) (fun _ => .rv) (rvValues '' D) (rvValues '' E) := by
  let P := pureRVPointRawEquiv D
  let Q := pureRVPointRawEquiv E
  let f := P.symm.trans (e.equiv.trans Q)
  have h := gammaRawRVGraph_definable e.graph
  have hs : Fin.append (fun _ : Fin a => SortTag.rv) (fun _ : Fin b => .rv) = (fun _ => .rv) := by
    funext j
    exact Fin.addCases (fun i => Fin.append_left _ _ i) (fun i => Fin.append_right _ _ i) j
  refine ⟨f,?_⟩
  rw [hs]
  convert h using 1
  ext w
  constructor
  · rintro ⟨r,rfl⟩
    exact ⟨(P.symm r).val,(e.equiv (P.symm r)).val,⟨P.symm r,rfl,rfl⟩,rfl⟩
  · rintro ⟨p,q,⟨u,rfl,rfl⟩,rfl⟩
    refine ⟨P u,?_⟩
    change Fin.append _ (rvValues (e.equiv (P.symm (P u))).val.2) = _
    rw [Equiv.symm_apply_apply]
    rfl

theorem pure_rv_point_sorted_iso_value {D : Set (Fin a → CanonicalRV.RVSort M)}
    {E : Set (Fin b → CanonicalRV.RVSort M)}
    (e : GammaIso B {q : Point (M := M) 0 a | q.2 ∈ D}
      {q : Point (M := M) 0 b | q.2 ∈ E})
    (u : {q : Point (M := M) 0 a | q.2 ∈ D}) :
    ((pureRVPointSortedIso e).equiv (pureRVPointRawEquiv D u)).val =
      rvValues (e.equiv u).val.2 := by
  change rvValues (e.equiv ((pureRVPointRawEquiv D).symm (pureRVPointRawEquiv D u))).val.2 = _
  rw [Equiv.symm_apply_apply]

end IntegrationInACVF.Section7.HK
