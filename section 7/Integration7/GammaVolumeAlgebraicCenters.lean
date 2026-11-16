module

public import Integration7.GammaCanonicalAdmissibilityRows
public import Integration7.ElementaryBlowupRestriction

@[expose] public section

/-! Original-base algebraicity of an actual blowup center. The carrier
and coordinate map remain those of the existing volume object. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4
open SpecialTransformations.Section7 (gammaVolumeValue)
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {S : Set M} {k : ℕ}

def GammaBlowupCenter (U : PositiveRVVolumeObject (M := M) S k) (B : Base (M := M)) : Prop :=
  ∀ u : U.underlying.obj.domain,
    AlgebraicAtBase ⟨Section6.coordinateBase B.real (Fin.last k) (U.underlying.obj.value u),B.gamma⟩
      .rv (U.underlying.obj.value u (Fin.last k)).val

theorem GammaBlowupCenter.restrict {U : PositiveRVVolumeObject (M := M) S k}
    (h : GammaBlowupCenter U B)
    (A : SpecialTransformations.DefinableGeometry.DefSet (rawRVSpace (M := M) U.underlying.obj.arity) S)
    (hA : A.carrier ⊆ U.underlying.obj.domain.carrier) : GammaBlowupCenter (U.restrict A hA) B :=
  fun u => h ⟨u.val,hA u.property⟩

theorem GammaBlowupCenter.canonical
    (hc : CanonicalStructure.IsCanonical (M := M))
    (U : FiniteRV.GammaObjectAt B S (k+1))
    (ω : VolumeForm (canonicalFiniteRVObject hc U.object).obj.domain)
    (hAd : GammaAdmissible U.toGamma.toGammaRVObject (Fin.last k)) :
    GammaBlowupCenter
      (⟨canonicalFiniteRVObject hc U.object,ω⟩ : PositiveRVVolumeObject (M := M) S k) B :=
  fun u => hAd.algebraic ⟨u.val,u.property⟩

theorem GammaBlowupCenter.schema_row {p : ℕ} {sp : Fin p → SortTag}
    (z : Fin p → M) (U : PositiveRVVolumeObject (M := M) S k) (hAd : BlowupAdmissible U)
    (hΓ : GammaBlowupCenter U ⟨B.real ∪ Set.range z,B.gamma⟩)
    (F : GammaRVVolumeSchema B p U.underlying.obj.arity k sp) (PU : RVVolumeSchemaRow U F z)
    (P : GammaFiniteGraphPresentation ⟨B.real ∪ Set.range z,B.gamma⟩ U.underlying.obj.arity (k+1)
      (F.object.rowDomain z) (F.object.rowVolume z)) : GammaAdmissible P.toGamma.toGammaRVObject (Fin.last k) := by
  constructor
  · intro u
    let t := gammaVolumeValue P.toGamma.toGammaRVObject u
    have ht := ((P.graph_iff u.val t).mp ⟨u,rfl,rfl⟩).2
    obtain ⟨v,_,hv⟩ := (PU.volume_iff _ _).mp ht
    change (t (Fin.last k)).val ≠ iRVZero
    rw [← hv]
    exact (rv_nonzero_iff_raw _).mp (hAd.nonzero v)
  · intro u
    let t := gammaVolumeValue P.toGamma.toGammaRVObject u
    have ht := ((P.graph_iff u.val t).mp ⟨u,rfl,rfl⟩).2
    obtain ⟨v,_,hv⟩ := (PU.volume_iff _ _).mp ht
    change AlgebraicAtBase ⟨Section6.coordinateBase (B.real ∪ Set.range z) (Fin.last k) t,B.gamma⟩
      .rv (t (Fin.last k)).val
    rw [← hv]
    exact hΓ v

end IntegrationInACVF.Section7
