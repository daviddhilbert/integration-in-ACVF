import IntegrationSection6.GammaRVGraphRaw
import IntegrationSection6.GammaNativeFiniteBounds

/-! Raw full-graph laws for actual Gamma RV isomorphisms. Reverse fibres
have cardinality at most one, and the two actual volume graphs satisfy
the literal RV weight identity. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {k : ℕ} {U V : GammaRVObject B k}

def gammaRawIsoGraph (e : GammaRVIso U V) : Set (Fin (rvObjectArity U.object+rvObjectArity V.object) → M) :=
  {z | ∃ u : rvObjectDomain U.object,
    Fin.append (fun j => (u.val j).val) (fun j => ((e.equiv u).val j).val) = z}

theorem gammaRawIsoGraph_definable (e : GammaRVIso U V) :
    DefinableOverBase B (fun _ => .rv) (gammaRawIsoGraph e) := by
  have h := gammaRawRVGraph_definable e.graph
  convert h using 1
  apply Set.ext
  intro z
  constructor
  · rintro ⟨u,hu⟩
    exact ⟨(Fin.elim0,u.val),(Fin.elim0,(e.equiv u).val),⟨u,rfl,rfl⟩,hu⟩
  · rintro ⟨p,q,⟨u,hp,hq⟩,hz⟩
    refine ⟨u,?_⟩
    rw [hp,hq]
    exact hz

theorem gammaRawIsoGraph_append_iff (e : GammaRVIso U V)
    (x : Fin (rvObjectArity U.object) → M) (y : Fin (rvObjectArity V.object) → M) :
    Fin.append x y ∈ gammaRawIsoGraph e ↔ ∃ u : rvObjectDomain U.object,
      (fun j => (u.val j).val) = x ∧ (fun j => ((e.equiv u).val j).val) = y := by
  constructor
  · rintro ⟨u,hu⟩
    refine ⟨u,funext (fun j => ?_),funext (fun j => ?_)⟩
    · simpa only [Fin.append_left] using congrFun hu (Fin.castAdd (rvObjectArity V.object) j)
    · simpa only [Fin.append_right] using congrFun hu (Fin.natAdd (rvObjectArity U.object) j)
  · rintro ⟨u,hx,hy⟩
    exact ⟨u,congrArg₂ Fin.append hx hy⟩

theorem gammaRawIsoGraph_unique (e : GammaRVIso U V)
    (x : Fin (rvObjectArity U.object) → M) (hx : x ∈ gammaRawObjectDomain U) :
    ∃! y : Fin (rvObjectArity V.object) → M, Fin.append x y ∈ gammaRawIsoGraph e := by
  obtain ⟨u,hu,hUnique⟩ := gammaRawObjectDomain_unique U x hx
  refine ⟨fun j => ((e.equiv u).val j).val,
    (gammaRawIsoGraph_append_iff e x _).mpr ⟨u,hu,rfl⟩,?_⟩
  intro y hy
  obtain ⟨v,hv,hvy⟩ := (gammaRawIsoGraph_append_iff e x y).mp hy
  have he := hUnique v hv
  exact hvy.symm.trans (congrArg (fun v => fun j => ((e.equiv v).val j).val) he)

theorem gammaRawIsoGraph_image (e : GammaRVIso U V)
    (y : Fin (rvObjectArity V.object) → M) :
    (∃ x, Fin.append x y ∈ gammaRawIsoGraph e) ↔ y ∈ gammaRawObjectDomain V := by
  constructor
  · rintro ⟨x,hx⟩
    obtain ⟨u,_,hu⟩ := (gammaRawIsoGraph_append_iff e x y).mp hx
    exact ⟨e.equiv u,hu⟩
  · rintro ⟨v,hv⟩
    refine ⟨fun j => ((e.equiv.symm v).val j).val,
      (gammaRawIsoGraph_append_iff e _ y).mpr ⟨e.equiv.symm v,rfl,?_⟩⟩
    simpa only [Equiv.apply_symm_apply] using hv

theorem gammaRawIsoGraph_fibre_bound (e : GammaRVIso U V)
    (y : Fin (rvObjectArity V.object) → M) :
    {x | Fin.append x y ∈ gammaRawIsoGraph e}.Finite ∧
      {x | Fin.append x y ∈ gammaRawIsoGraph e}.ncard ≤ 1 := by
  apply Set.encard_le_coe_iff_finite_ncard_le.mp
  apply Set.encard_le_one_iff.mpr
  intro x x' hx hx'
  obtain ⟨u,hu,hy⟩ := (gammaRawIsoGraph_append_iff e x y).mp hx
  obtain ⟨u',hu',hy'⟩ := (gammaRawIsoGraph_append_iff e x' y).mp hx'
  have he : e.equiv u = e.equiv u' := by
    apply Subtype.ext
    funext j
    apply Subtype.ext
    exact congrFun (hy.trans hy'.symm) j
  have he' := e.equiv.injective he
  exact hu.symm.trans ((congrArg (fun u => fun j => (u.val j).val) he').trans hu')

theorem gammaRawIsoGraph_weight (e : GammaRVIso U V)
    (x : Fin (rvObjectArity U.object) → M) (y : Fin (rvObjectArity V.object) → M)
    (s t : Fin k → M) (hH : Fin.append x y ∈ gammaRawIsoGraph e)
    (hU : Fin.append x s ∈ gammaRawObjectVolume U)
    (hV : Fin.append y t ∈ gammaRawObjectVolume V) : rawWeight s = rawWeight t := by
  obtain ⟨u,hu,hy⟩ := (gammaRawIsoGraph_append_iff e x y).mp hH
  obtain ⟨u',hu',hs⟩ := (gammaRawObjectVolume_append_iff U x s).mp hU
  obtain ⟨v,hv,ht⟩ := (gammaRawObjectVolume_append_iff V y t).mp hV
  have heU : u' = u := (gammaRawObjectDomain_unique U x ⟨u,hu⟩).unique hu' hu
  have heV : v = e.equiv u := (gammaRawObjectDomain_unique V y ⟨e.equiv u,hy⟩).unique hv hy
  rw [heU] at hs
  rw [heV] at ht
  have hw := e.weight u
  rw [hs,ht] at hw
  exact hw

end IntegrationInACVF.Section6
