import Integration7.VolumeBlowupClasses

/-! Uniform coproduct operations, including ordinary RV[0]. All
structural maps below are actual definable isomorphisms. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4

namespace IntegrationInACVF.Section7

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def rvVolumeCoprod (S : Set M) : (n : ℕ) → RVVolumeObject (M := M) S n →
    RVVolumeObject (M := M) S n → RVVolumeObject (M := M) S n
  | 0,U,V => rvFiniteCoprodObject U V
  | _+1,U,V => U.coprod V

def rvVolumeEmpty (S : Set M) : (n : ℕ) → RVVolumeObject (M := M) S n
  | 0 => rvFiniteEmpty S 0
  | k+1 => PositiveRVVolumeObject.empty S k

def rvVolumeCoprodIso
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {n : ℕ} {U U' V V' : RVVolumeObject (M := M) (C.base : Set M) n}
    (f : RVVolumeIsoInDegree (C.base : Set M) n U U')
    (g : RVVolumeIsoInDegree (C.base : Set M) n V V') :
    RVVolumeIsoInDegree (C.base : Set M) n (rvVolumeCoprod _ n U V) (rvVolumeCoprod _ n U' V') := by
  cases n with
  | zero => exact rvFiniteIsoOfAmbient (rvCoprodIsoExplicit
      ((finiteVolumeProperty (C.base : Set M) 0).ι.mapIso f)
      ((finiteVolumeProperty (C.base : Set M) 0).ι.mapIso g))
  | succ k => exact f.coprod hc C g

def rvVolumeCoprodAssocIso
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) {n : ℕ}
    (U V W : RVVolumeObject (M := M) (C.base : Set M) n) :
    RVVolumeIsoInDegree (C.base : Set M) n
      (rvVolumeCoprod _ n (rvVolumeCoprod _ n U V) W)
      (rvVolumeCoprod _ n U (rvVolumeCoprod _ n V W)) := by
  cases n with
  | zero => exact rvFiniteIsoOfAmbient (rvCoprodAssocExplicit U.obj V.obj W.obj)
  | succ k => exact volumeCoprodAssoc hc C U V W

def rvVolumeCoprodSwapIso
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) {n : ℕ}
    (U V : RVVolumeObject (M := M) (C.base : Set M) n) :
    RVVolumeIsoInDegree (C.base : Set M) n (rvVolumeCoprod _ n U V) (rvVolumeCoprod _ n V U) := by
  cases n with
  | zero => exact rvFiniteIsoOfAmbient (rvCoprodSwapExplicit U.obj V.obj)
  | succ k => exact volumeCoprodSwap hc C U V

def rvOrdinaryCoprodRightUnit (S : Set M) {k : ℕ} (U : RVObject (M := M) S k) :
    rvCoprodObject U (RVObject.empty S k) ≅ U := by
  let E := RVObject.empty (M := M) S k
  let f := rvCoprodLeftMap U E
  have hf : Function.Bijective f := by
    constructor
    · intro x y h
      exact Subtype.ext (rvLeftTag_injective E.arity
        (congrArg (fun z : (rvCoprodObject U E).domain => z.val) h))
    · rintro ⟨x,⟨u,hu⟩ | ⟨v,hv⟩⟩
      · exact ⟨u,Subtype.ext hu⟩
      · exact False.elim v.property
  exact (rvIsoOfVolumePreservingBijection f hf (rvCoprod_value_left U E)).symm

def rvVolumeCoprodRightUnitIso
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) {n : ℕ}
    (U : RVVolumeObject (M := M) (C.base : Set M) n) :
    RVVolumeIsoInDegree (C.base : Set M) n (rvVolumeCoprod _ n U (rvVolumeEmpty _ n)) U := by
  cases n with
  | zero =>
    exact rvFiniteIsoOfAmbient (rvOrdinaryCoprodRightUnit (C.base : Set M) U.obj)
  | succ k => exact volumeCoprodRightUnit hc C U

def rvVolumeCoprodLeftUnitIso
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) {n : ℕ}
    (U : RVVolumeObject (M := M) (C.base : Set M) n) :
    RVVolumeIsoInDegree (C.base : Set M) n (rvVolumeCoprod _ n (rvVolumeEmpty _ n) U) U := by
  cases n with
  | zero =>
    let e : rvFiniteCoprodObject (rvFiniteEmpty (C.base : Set M) 0) U ≅
        rvFiniteCoprodObject U (rvFiniteEmpty (C.base : Set M) 0) :=
      rvFiniteIsoOfAmbient (rvCoprodSwapExplicit (RVObject.empty _ 0) U.obj)
    exact e.trans (rvVolumeCoprodRightUnitIso hc C (n := 0) U)
  | succ k => exact volumeCoprodLeftUnit hc C U

theorem muIsp_coprod
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {n : ℕ} {U U' V V' : RVVolumeObject (M := M) (C.base : Set M) n}
    (h : MuIsp (C.base : Set M) n U U') (g : MuIsp (C.base : Set M) n V V') :
    MuIsp (C.base : Set M) n (rvVolumeCoprod _ n U V) (rvVolumeCoprod _ n U' V') := by
  cases n with
  | zero =>
    obtain ⟨f⟩ := h
    obtain ⟨e⟩ := g
    exact ⟨rvVolumeCoprodIso hc C (n := 0) (U := U) (U' := U') (V := V) (V' := V') f e⟩
  | succ k => exact VolumeBlowupEquivalent.coprod hc C h g

end IntegrationInACVF.Section7
