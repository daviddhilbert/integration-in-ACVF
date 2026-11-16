module

public import Integration7.ElementaryBlowupConstruction
public import Integration7.VolumeFormScalarArithmetic
public import Integration7.RVCoordinateSelection
public import IntegrationSection6.AlgebraicFibres

@[expose] public section

/-! An admissible last volume coordinate may be dropped while retaining
finite volume fibres. In positive remaining degree its contribution moves
into the density, as in the factorization preceding Theorem7.13. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {k : ℕ}

theorem admissible_head_volume_fibres_finite
    (C : BaseContext M) (U : PositiveRVVolumeObject (M := M) (C.base : Set M) k)
    (h : BlowupAdmissible U) (t : Fin k → CanonicalRV.RVSort M) :
    {u : U.underlying.obj.domain | U.underlying.obj.value u ∘ Fin.castSucc = t}.Finite := by
  let t' : Fin (k+1) → CanonicalRV.RVSort M := Fin.snoc t 0
  let T := {r | (∃ u : U.underlying.obj.domain, U.underlying.obj.value u = r) ∧
    ∀ j, j ≠ Fin.last k → r j = t' j}
  have hT : T.Finite := h.toOrdinary.finite_label_fibres C.uncountable.le C.saturated C.small t'
  have hAll : (⋃ r ∈ T,
      {u : U.underlying.obj.domain | U.underlying.obj.volume u = ⟨r,Set.mem_univ _⟩}).Finite :=
    hT.biUnion (fun r _ => U.underlying.property ⟨r,Set.mem_univ _⟩)
  apply hAll.subset
  intro u hu
  apply Set.mem_iUnion.mpr
  refine ⟨U.underlying.obj.value u,Set.mem_iUnion.mpr ⟨?_,rfl⟩⟩
  refine ⟨⟨u,rfl⟩,?_⟩
  intro j hj
  refine Fin.lastCases (fun hj => False.elim (hj rfl)) (fun i _ => ?_) j hj
  simpa only [t',Fin.snoc_castSucc,Function.comp_apply] using congrFun hu i

def admissibleHeadFiniteObject
    (C : BaseContext M) (U : PositiveRVVolumeObject (M := M) (C.base : Set M) k)
    (h : BlowupAdmissible U) : RVFiniteObject (M := M) (C.base : Set M) k where
  obj := {
    arity := U.underlying.obj.arity
    domain := U.underlying.obj.domain
    volume := (rvCoordinateSelectMap (C.base : Set M) (Fin.castSucc : Fin k → Fin (k+1))).comp
      U.underlying.obj.volume }
  property t := (admissible_head_volume_fibres_finite C U h t.val).subset
    (fun _ hu => congrArg Subtype.val hu)

def admissibleHeadVolumeFactor
    (C : BaseContext M) (U : PositiveRVVolumeObject (M := M) (C.base : Set M) (k+1))
    (h : BlowupAdmissible U) : PositiveRVVolumeObject (M := M) (C.base : Set M) k where
  underlying := admissibleHeadFiniteObject C U h
  form := U.form.mul {
    map := (rvCoordinateSelectMap (C.base : Set M) (fun _ : Fin 1 => Fin.last (k+1))).comp
      U.underlying.obj.volume
    nonzero u := h.nonzero u }

theorem admissible_head_factor_coordinates
    (C : BaseContext M) (U : PositiveRVVolumeObject (M := M) (C.base : Set M) (k+1))
    (h : BlowupAdmissible U) (u : (admissibleHeadVolumeFactor C U h).underlying.obj.domain) :
    (admissibleHeadVolumeFactor C U h).underlying.obj.value u =
      U.underlying.obj.value u ∘ Fin.castSucc := rfl

theorem admissible_head_factor_density
    (C : BaseContext M) (U : PositiveRVVolumeObject (M := M) (C.base : Set M) (k+1))
    (h : BlowupAdmissible U) (u : (admissibleHeadVolumeFactor C U h).underlying.obj.domain) :
    (admissibleHeadVolumeFactor C U h).form.value u =
      U.form.value u * U.underlying.obj.value u (Fin.last (k+1)) := rfl

end IntegrationInACVF.Section7
