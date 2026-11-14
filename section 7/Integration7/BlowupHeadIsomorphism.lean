import Integration7.ElementaryBlowupConstruction
import Integration7.RVCoordinateSelection
import Integration7.NondegenerateFiniteIso

/-! Admissibility makes the unchanged head coordinates a finite-volume
map. This uses actual algebraic label fibres and the original finite
volume fibres, with the genuine small-base saturation assumptions. -/

set_option backward.isDefEq.respectTransparency false
noncomputable section

open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {k : ℕ}

def blowupHeadVolume (U : PositiveRVVolumeObject (M := M) S k) :
    Map U.essential.obj.domain (DefSet.univ (rawRVSpace (M := M) k) S) :=
  (rvCoordinateSelectMap S Fin.castSucc).comp U.essential.obj.volume

theorem blowupHeadVolume_finite (C : BaseContext M)
    (U : PositiveRVVolumeObject (M := M) (C.base : Set M) k) (hU : BlowupAdmissible U) :
    (blowupHeadVolume U).FiniteFibres := by
  intro t
  let t' : Fin (k + 1) → CanonicalRV.RVSort M := Fin.snoc t.val 1
  let R := {r | (∃ u : U.underlying.obj.domain, U.underlying.obj.value u = r) ∧
    ∀ j, j ≠ Fin.last k → r j = t' j}
  have hR : R.Finite := hU.toOrdinary.finite_label_fibres
    C.uncountable.le C.saturated C.small t'
  apply (hR.biUnion (fun r _ =>
    U.essential.property ⟨r, Set.mem_univ _⟩)).subset
  intro u hu
  refine Set.mem_iUnion.mpr ⟨U.essential.obj.value u, Set.mem_iUnion.mpr ⟨?_, rfl⟩⟩
  refine ⟨⟨⟨u.val, rvEssentialLabels_subset U.underlying.obj u.property⟩, rfl⟩, ?_⟩
  intro j hj
  obtain ⟨i, rfl⟩ := Fin.eq_castSucc_of_ne_last hj
  have he := congrArg (fun z : DefSet.univ (rawRVSpace (M := M) k) (C.base : Set M) => z.val i) hu
  change U.essential.obj.value u i.castSucc = t.val i at he
  simpa only [t', Fin.snoc_castSucc] using he

def blowupHeadObject (C : BaseContext M)
    (U : PositiveRVVolumeObject (M := M) (C.base : Set M) k) (hU : BlowupAdmissible U) :
    RVFiniteObject (M := M) (C.base : Set M) k :=
  ⟨⟨U.essential.obj.arity, U.essential.obj.domain, blowupHeadVolume U⟩,
    blowupHeadVolume_finite C U hU⟩

@[simp] theorem blowupHeadObject_value (C : BaseContext M)
    (U : PositiveRVVolumeObject (M := M) (C.base : Set M) k) (hU : BlowupAdmissible U)
    (u : U.essential.obj.domain) :
    (blowupHeadObject C U hU).obj.value u = U.essential.obj.value u ∘ Fin.castSucc := rfl

def blowupHeadIso (C : BaseContext M)
    {U V : PositiveRVVolumeObject (M := M) (C.base : Set M) k}
    (f : RVVolumeIso U V) (hU : BlowupAdmissible U) (hV : BlowupAdmissible V) :
    blowupHeadObject C U hU ≅ blowupHeadObject C V hV := by
  let F : Map U.essential.obj.domain V.essential.obj.domain := finiteIsoMap f.iso
  exact finiteIsoOfNondegenerateBijection
    (U := blowupHeadObject C U hU) (V := blowupHeadObject C V hV)
    F (finiteIsoMap_bijective f.iso)
    (fun u i => U.essential_nonzero u i.castSucc)
    (fun v i => V.essential_nonzero v i.castSucc)

@[simp] theorem blowupHeadIso_map (C : BaseContext M)
    {U V : PositiveRVVolumeObject (M := M) (C.base : Set M) k}
    (f : RVVolumeIso U V) (hU : BlowupAdmissible U) (hV : BlowupAdmissible V)
    (u : U.essential.obj.domain) :
    finiteIsoMap (blowupHeadIso C f hU hV) u = finiteIsoMap f.iso u := rfl

end IntegrationInACVF.Section7
