module

public import Integration7.GammaPermutedVolumeObjects
public import Integration7.GammaGeometricCommonWitnesses

@[expose] public section

/-! Geometric common schema witnesses transport through a simultaneous
permutation of their full volume tuples, with unchanged density rows. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5 (RV)

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {S : Set M} {p a b k : ℕ} {sp : Fin p → SortTag}

theorem RVVolumeSchemaRow.permuteVolume
    (U : PositiveRVVolumeObject (M := M) S k)
    (F F' : GammaRVVolumeSchema B p U.underlying.obj.arity k sp) (z : Fin p → M)
    (P : RVVolumeSchemaRow U F z) (e : Equiv.Perm (Fin (k+1)))
    (hV : ∀ r y, F'.object.rowVolume z r y ↔ F.object.rowVolume z r (y ∘ e.symm))
    (hD : ∀ r w, F'.rowDensity z r w ↔ F.rowDensity z r w) :
    RVVolumeSchemaRow (U.permuteVolume e) F' z := by
  constructor
  · intro r y
    rw [hV,P.volume_iff]
    constructor
    · rintro ⟨u,hu,hv⟩
      refine ⟨u,hu,?_⟩
      change U.underlying.obj.value u ∘ e = y
      rw [hv]
      funext i
      exact congrArg y (e.symm_apply_apply i)
    · rintro ⟨u,hu,hv⟩
      refine ⟨u,hu,?_⟩
      funext i
      change U.underlying.obj.value u i = y (e.symm i)
      have hi := congrFun hv (e.symm i)
      change U.underlying.obj.value u (e (e.symm i)) = y (e.symm i) at hi
      simpa only [e.apply_symm_apply] using hi
  · intro r w
    exact (hD r w).trans (P.density_iff r w)

theorem GammaRVVolumeSchema.commonByGammaGeometry_permute_volume
    (hc : CanonicalStructure.IsCanonical (M := M))
    (F F' : GammaRVVolumeSchema B p a k sp) (G G' : GammaRVVolumeSchema B p b k sp)
    (z : Fin p → M) (e : Equiv.Perm (Fin (k+1)))
    (hFV : ∀ r y, F'.object.rowVolume z r y ↔ F.object.rowVolume z r (y ∘ e.symm))
    (hFD : ∀ r w, F'.rowDensity z r w ↔ F.rowDensity z r w)
    (hGV : ∀ r y, G'.object.rowVolume z r y ↔ G.object.rowVolume z r (y ∘ e.symm))
    (hGD : ∀ r w, G'.rowDensity z r w ↔ G.rowDensity z r w)
    (hGeom : F.commonByGammaGeometry G z) : F'.commonByGammaGeometry G' z := by
  obtain ⟨C,U,V,ha,hb,PU,PV,h⟩ := hGeom
  subst a b
  exact ⟨C,⟨U.val.permuteVolume e,U.property.permuteVolume hc e⟩,
    ⟨V.val.permuteVolume e,V.property.permuteVolume hc e⟩,rfl,rfl,
    PU.permuteVolume U.val F F' z e hFV hFD,
    PV.permuteVolume V.val G G' z e hGV hGD,h.permuteVolume hc C e⟩

end IntegrationInACVF.Section7
