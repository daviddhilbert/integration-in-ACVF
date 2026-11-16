module

public import Integration7.HKVolumeCoproducts
public import Integration7.VolumeCoproductIsomorphism

@[expose] public section

/-! The actual coproduct bijections preserve the full zero-degree form.
Positive-degree isomorphisms reuse their established geometric proofs. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7.HK
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M}

def zeroCoprodIso {U U' V V' : ZeroRVVolumeObject (M := M) S}
    (f : ZeroRVVolumeIso U U') (g : ZeroRVVolumeIso V V') :
    ZeroRVVolumeIso (coprod S 0 U V) (coprod S 0 U' V') where
  iso := rvFiniteIsoOfAmbient (rvCoprodIsoExplicit
    ((finiteVolumeProperty S 0).ι.mapIso f.iso) ((finiteVolumeProperty S 0).ι.mapIso g.iso))
  density w := by
    rcases zero_coprod_cases U V w with ⟨u,rfl⟩ | ⟨v,rfl⟩
    · change (coprod S 0 U V).form.value (rvCoprodLeftMap _ _ u) =
        (coprod S 0 U' V').form.value ((rvCoprodIsoExplicit
          ((finiteVolumeProperty S 0).ι.mapIso f.iso)
          ((finiteVolumeProperty S 0).ι.mapIso g.iso)).hom.map (rvCoprodLeftMap _ _ u))
      rw [rvCoprodIsoExplicit_left]
      exact (coprod_density_left 0 U V u).trans
        ((f.density u).trans (coprod_density_left 0 U' V' (finiteIsoMap f.iso u)).symm)
    · change (coprod S 0 U V).form.value (rvCoprodRightMap _ _ v) =
        (coprod S 0 U' V').form.value ((rvCoprodIsoExplicit
          ((finiteVolumeProperty S 0).ι.mapIso f.iso)
          ((finiteVolumeProperty S 0).ι.mapIso g.iso)).hom.map (rvCoprodRightMap _ _ v))
      rw [rvCoprodIsoExplicit_right]
      exact (coprod_density_right 0 U V v).trans
        ((g.density v).trans (coprod_density_right 0 U' V' (finiteIsoMap g.iso v)).symm)

def zeroCoprodSwap (U V : ZeroRVVolumeObject (M := M) S) :
    ZeroRVVolumeIso (coprod S 0 U V) (coprod S 0 V U) where
  iso := rvFiniteIsoOfAmbient (rvCoprodSwapExplicit U.underlying.obj V.underlying.obj)
  density w := by
    rcases zero_coprod_cases U V w with ⟨u,rfl⟩ | ⟨v,rfl⟩
    · change (coprod S 0 U V).form.value (rvCoprodLeftMap _ _ u) =
        (coprod S 0 V U).form.value ((rvCoprodSwapExplicit _ _).hom.map (rvCoprodLeftMap _ _ u))
      rw [rvCoprodSwapExplicit_left]
      exact (coprod_density_left 0 U V u).trans (coprod_density_right 0 V U u).symm
    · change (coprod S 0 U V).form.value (rvCoprodRightMap _ _ v) =
        (coprod S 0 V U).form.value ((rvCoprodSwapExplicit _ _).hom.map (rvCoprodRightMap _ _ v))
      rw [rvCoprodSwapExplicit_right]
      exact (coprod_density_right 0 U V v).trans (coprod_density_left 0 V U v).symm

def zeroCoprodAssoc (U V W : ZeroRVVolumeObject (M := M) S) :
    ZeroRVVolumeIso (coprod S 0 (coprod S 0 U V) W) (coprod S 0 U (coprod S 0 V W)) where
  iso := rvFiniteIsoOfAmbient (rvCoprodAssocExplicit U.underlying.obj V.underlying.obj W.underlying.obj)
  density z := by
    rcases zero_coprod_cases (coprod S 0 U V) W z with ⟨a,rfl⟩ | ⟨w,rfl⟩
    · rcases zero_coprod_cases U V a with ⟨u,rfl⟩ | ⟨v,rfl⟩
      · change (coprod S 0 (coprod S 0 U V) W).form.value
          (rvCoprodLeftMap _ _ (rvCoprodLeftMap _ _ u)) =
          (coprod S 0 U (coprod S 0 V W)).form.value
          ((rvCoprodAssocExplicit _ _ _).hom.map (rvCoprodLeftMap _ _ (rvCoprodLeftMap _ _ u)))
        rw [rvCoprodAssocExplicit_left]
        exact ((coprod_density_left 0 (coprod S 0 U V) W _).trans
          (coprod_density_left 0 U V u)).trans (coprod_density_left 0 U (coprod S 0 V W) u).symm
      · change (coprod S 0 (coprod S 0 U V) W).form.value
          (rvCoprodLeftMap _ _ (rvCoprodRightMap _ _ v)) =
          (coprod S 0 U (coprod S 0 V W)).form.value
          ((rvCoprodAssocExplicit _ _ _).hom.map (rvCoprodLeftMap _ _ (rvCoprodRightMap _ _ v)))
        rw [rvCoprodAssocExplicit_middle]
        exact ((coprod_density_left 0 (coprod S 0 U V) W _).trans
          (coprod_density_right 0 U V v)).trans
          (((coprod_density_right 0 U (coprod S 0 V W) _).trans
            (coprod_density_left 0 V W v)).symm)
    · change (coprod S 0 (coprod S 0 U V) W).form.value (rvCoprodRightMap _ _ w) =
        (coprod S 0 U (coprod S 0 V W)).form.value
        ((rvCoprodAssocExplicit _ _ _).hom.map (rvCoprodRightMap _ _ w))
      rw [rvCoprodAssocExplicit_right]
      exact (coprod_density_right 0 (coprod S 0 U V) W w).trans
        (((coprod_density_right 0 U (coprod S 0 V W) _).trans (coprod_density_right 0 V W w)).symm)

def zeroCoprodEmptyEmbedding (U : ZeroRVVolumeObject (M := M) S) :
    ZeroRVVolumeIso U (coprod S 0 U (empty S 0)) := by
  let E := empty (M := M) S 0
  let F := rvCoprodLeftMap U.underlying.obj E.underlying.obj
  have hF : Function.Bijective F := by
    constructor
    · intro a b he
      exact Subtype.ext (rvLeftTag_injective E.underlying.obj.arity
        (congrArg (fun w : (coprod S 0 U E).underlying.obj.domain => w.val) he))
    · intro w
      rcases zero_coprod_cases U E w with ⟨u,hu⟩ | ⟨v,hv⟩
      · exact ⟨u,hu⟩
      · exact False.elim v.property
  exact ZeroRVVolumeIso.ofBijection F hF (fun u => (coprod_density_left 0 U E u).symm)

def coprodIso (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {n : ℕ} {U U' V V' : RVVolumeObject (M := M) (C.base : Set M) n}
    (f : rvVolumeIsoInDegree (C.base : Set M) n U U')
    (g : rvVolumeIsoInDegree (C.base : Set M) n V V') :
    rvVolumeIsoInDegree (C.base : Set M) n (coprod _ n U V) (coprod _ n U' V') := by
  cases n with
  | zero => exact zeroCoprodIso f g
  | succ k => exact f.coprod hc C g

def coprodAssocIso (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {n : ℕ} (U V W : RVVolumeObject (M := M) (C.base : Set M) n) :
    rvVolumeIsoInDegree (C.base : Set M) n
      (coprod _ n (coprod _ n U V) W) (coprod _ n U (coprod _ n V W)) := by
  cases n with
  | zero => exact zeroCoprodAssoc U V W
  | succ k => exact volumeCoprodAssoc hc C U V W

def coprodSwapIso (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {n : ℕ} (U V : RVVolumeObject (M := M) (C.base : Set M) n) :
    rvVolumeIsoInDegree (C.base : Set M) n (coprod _ n U V) (coprod _ n V U) := by
  cases n with
  | zero => exact zeroCoprodSwap U V
  | succ k => exact volumeCoprodSwap hc C U V

def coprodRightUnitIso (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {n : ℕ} (U : RVVolumeObject (M := M) (C.base : Set M) n) :
    rvVolumeIsoInDegree (C.base : Set M) n (coprod _ n U (empty _ n)) U := by
  cases n with
  | zero => exact (zeroCoprodEmptyEmbedding U).symm
  | succ k => exact volumeCoprodRightUnit hc C U

def coprodLeftUnitIso (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {n : ℕ} (U : RVVolumeObject (M := M) (C.base : Set M) n) :
    rvVolumeIsoInDegree (C.base : Set M) n (coprod _ n (empty _ n) U) U := by
  cases n with
  | zero => exact (zeroCoprodSwap _ U).trans (zeroCoprodEmptyEmbedding U).symm
  | succ k => exact volumeCoprodLeftUnit hc C U

end IntegrationInACVF.Section7.HK
