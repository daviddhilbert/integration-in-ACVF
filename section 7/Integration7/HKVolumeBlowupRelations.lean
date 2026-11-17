module

public import Integration7.HKVolumeIsoOperations
public import Integration7.HKWeightedZeroBlowupCongruence
public import Integration7.HKRVProductIsomorphisms
public import Integration7.VolumeBlowupRightProducts

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! The corrected common-blowup relation has exact weighted isomorphism
in degree zero, and the established common-blowup relation in positive degree. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4

namespace IntegrationInACVF.Section7.HK
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def MuIsp (S : Set M) : (n : ℕ) → RVVolumeObject (M := M) S n → RVVolumeObject (M := M) S n → Prop
  | 0,U,V => Nonempty (ZeroRVVolumeIso U V)
  | _+1,U,V => VolumeBlowupEquivalent U V

theorem muIsp_refl (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {n : ℕ} (U : RVVolumeObject (M := M) (C.base : Set M) n) : MuIsp (C.base : Set M) n U U := by
  cases n with
  | zero => exact ⟨ZeroRVVolumeIso.refl U⟩
  | succ k => exact VolumeBlowupEquivalent.refl hc C U

theorem muIsp_symm (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {n : ℕ} {U V : RVVolumeObject (M := M) (C.base : Set M) n}
    (h : MuIsp (C.base : Set M) n U V) : MuIsp (C.base : Set M) n V U := by
  cases n with
  | zero => obtain ⟨e⟩ := h; exact ⟨e.symm⟩
  | succ k => exact VolumeBlowupEquivalent.symm hc C h

theorem muIsp_trans (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {n : ℕ} {U V W : RVVolumeObject (M := M) (C.base : Set M) n}
    (h : MuIsp (C.base : Set M) n U V) (g : MuIsp (C.base : Set M) n V W) :
    MuIsp (C.base : Set M) n U W := by
  cases n with
  | zero => obtain ⟨e⟩ := h; obtain ⟨f⟩ := g; exact ⟨e.trans f⟩
  | succ k => exact VolumeBlowupEquivalent.trans hc C h g

def muIspSetoid (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) (n : ℕ) :
    Setoid (RVVolumeObject (M := M) (C.base : Set M) n) where
  r := MuIsp (C.base : Set M) n
  iseqv := ⟨muIsp_refl hc C,muIsp_symm hc C,muIsp_trans hc C⟩

theorem muIsp_coprod (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {n : ℕ} {U U' V V' : RVVolumeObject (M := M) (C.base : Set M) n}
    (h : MuIsp (C.base : Set M) n U U') (g : MuIsp (C.base : Set M) n V V') :
    MuIsp (C.base : Set M) n (coprod _ n U V) (coprod _ n U' V') := by
  cases n with
  | zero => obtain ⟨f⟩ := h; obtain ⟨e⟩ := g; exact ⟨zeroCoprodIso f e⟩
  | succ k => exact VolumeBlowupEquivalent.coprod hc C h g

theorem muIsp_product (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {n m : ℕ} {U U' : RVVolumeObject (M := M) (C.base : Set M) n}
    {V V' : RVVolumeObject (M := M) (C.base : Set M) m}
    (h : MuIsp (C.base : Set M) n U U') (g : MuIsp (C.base : Set M) m V V') :
    MuIsp (C.base : Set M) (n+m) (product _ n m U V) (product _ n m U' V') := by
  cases n with
  | zero =>
    cases m with
    | zero => obtain ⟨f⟩ := h; obtain ⟨e⟩ := g; exact ⟨zeroZeroProductIso f e⟩
    | succ m =>
      obtain ⟨f⟩ := h
      exact ((VolumeBlowupEquivalent.of_iso C (productZeroPositiveIso hc C U V)).trans hc C
        ((weightedZeroProdEquivalent hc C f g).reindexDegree hc C (Nat.zero_add m))).trans hc C
          (VolumeBlowupEquivalent.of_iso C ((productZeroPositiveIso hc C U' V').symm hc C))
  | succ n =>
    cases m with
    | zero =>
      obtain ⟨e⟩ := g
      exact ((VolumeBlowupEquivalent.of_iso C (productPositiveZeroIso hc C U V)).trans hc C
        (weightedProdZeroEquivalent hc C h e)).trans hc C
          (VolumeBlowupEquivalent.of_iso C ((productPositiveZeroIso hc C U' V').symm hc C))
    | succ m => exact h.prod hc C g

end IntegrationInACVF.Section7.HK
