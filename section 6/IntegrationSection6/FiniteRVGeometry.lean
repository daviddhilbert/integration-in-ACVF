import IntegrationSection6.FiniteCongruence
import IntegrationSection6.SpecialChainBlowup
import Section4.RVFiniteScissors

/-! Public Section6 geometry is only RV[k], the inherited finite-volume
full subcategory. Every object of an iterated blowup is bundled in RV[k].
Ambient-object arguments are implementation support, not additional targets. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
namespace IntegrationInACVF.Section6.FiniteRV
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {S : Set M} {k : ℕ}

abbrev Admissible (U : RVFiniteObject (M := M) S k) (i : Fin k) :=
  IntegrationInACVF.Section6.Admissible U.obj i

abbrev ElementaryBlowup (U V : RVFiniteObject (M := M) S k) :=
  IntegrationInACVF.Section6.ElementaryBlowup U.obj V.obj

abbrev Blowup (U V : RVFiniteObject (M := M) S k) :=
  IntegrationInACVF.Section6.Blowup U.obj V.obj

/-- Every intermediate object is an actual object of RV[k]. -/
inductive IteratedBlowup : ℕ → RVFiniteObject (M := M) S k → RVFiniteObject (M := M) S k → Prop
  | zero {U V} : Nonempty (U ≅ V) → IteratedBlowup 0 U V
  | cons {r U V W} : Blowup U V → IteratedBlowup r V W → IteratedBlowup (r+1) U W

def Isp (U V : RVFiniteObject (M := M) S k) : Prop :=
  ∃ r s A B, IteratedBlowup r U A ∧ IteratedBlowup s V B ∧ Nonempty (A ≅ B)

def elementary {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (hsmall : Cardinal.mk S < κ)
    (U : RVFiniteObject (M := M) S k) (i : Fin k) (h : Admissible U i) :
    RVFiniteObject (M := M) S k :=
  ⟨IntegrationInACVF.Section6.elementary U.obj i,
    elementary_finite_volume hκ hs hsmall U.obj i h U.property⟩

theorem IteratedBlowup.toAmbient {r : ℕ} {U V : RVFiniteObject (M := M) S k}
    (h : IteratedBlowup r U V) : IntegrationInACVF.Section6.IteratedBlowup r U.obj V.obj := by
  induction h with
  | zero he =>
    obtain ⟨e⟩ := he
    exact .zero ⟨(finiteVolumeProperty S k).ι.mapIso e⟩
  | cons h _ ih => exact .cons h ih

theorem ambientChain_toFinite {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (hsmall : Cardinal.mk S < κ)
    {r : ℕ} {U V : RVObject (M := M) S k}
    (h : IntegrationInACVF.Section6.IteratedBlowup r U V) :
    ∀ hU : U.volume.FiniteFibres, ∀ hV : V.volume.FiniteFibres,
      IteratedBlowup r ⟨U,hU⟩ ⟨V,hV⟩ := by
  induction h with
  | zero he =>
    intro hU hV
    exact .zero (he.map rvFiniteIsoOfAmbient)
  | cons h _ ih =>
    intro hU hV
    exact .cons h (ih (h.finite_volume hκ hs hsmall hU) hV)

theorem isp_iff_finiteIsp {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (hsmall : Cardinal.mk S < κ)
    (U V : RVFiniteObject (M := M) S k) : Isp U V ↔ finiteIsp U V := by
  constructor
  · rintro ⟨r,s,A,B,hU,hV,⟨e⟩⟩
    exact ⟨r,s,A.obj,B.obj,hU.toAmbient,hV.toAmbient,⟨(finiteVolumeProperty S k).ι.mapIso e⟩⟩
  · intro h
    obtain ⟨r,s,A,B,hU,hV,hA,hB,he⟩ := finiteIsp_witnesses hκ hs hsmall h
    exact ⟨r,s,⟨A,hA⟩,⟨B,hB⟩,
      ambientChain_toFinite hκ hs hsmall hU U.property hA,
      ambientChain_toFinite hκ hs hsmall hV V.property hB,he.map rvFiniteIsoOfAmbient⟩

end IntegrationInACVF.Section6.FiniteRV
