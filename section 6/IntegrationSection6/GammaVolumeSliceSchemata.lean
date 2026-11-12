import IntegrationSection6.GammaVolumeSliceCoordinates
import IntegrationSection6.GammaRelationalObjectSchemata

/-! Every RV[e+k] object is canonically a full Gamma family of RV[k]
volume slices over RV[e]. All rows have finite fibres, with no chosen
uniform cardinality bound. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.rawRVSpace SpecialTransformations.Section4.vfSpace
  SpecialTransformations.Section4.rvSpace SpecialTransformations.Section4.realSpace
  SpecialTransformations.Milestone0.sortEval SpecialTransformations.DefinableGeometry.Space.ofEmbedding
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {e k : ℕ}

def gammaVolumeSliceSchema (U : GammaRVFiniteObject B (e+k)) :
    GammaFiniteRVSchema B e (rvObjectArity U.object) k (fun _ => .rv) :=
  (gammaVolumeSliceFormula U).graphSchema

theorem gammaVolumeSliceSchema_volume (U : GammaRVFiniteObject B (e+k))
    (t : Fin e → RV (M := M)) (x : Fin (rvObjectArity U.object) → RV (M := M))
    (y : Fin k → RV (M := M)) :
    (gammaVolumeSliceSchema U).rowVolume (fun j => (t j).val) x y ↔
      ∃ u : rvObjectDomain U.object, u.val = x ∧ gammaVolumeValue U.toGammaRVObject u = Fin.append t y :=
  gammaVolumeSliceFormula_row U t x y

theorem gammaVolumeSliceSchema_domain (U : GammaRVFiniteObject B (e+k))
    (t : Fin e → RV (M := M)) (x : Fin (rvObjectArity U.object) → RV (M := M)) :
    x ∈ (gammaVolumeSliceSchema U).rowDomain (fun j => (t j).val) ↔
      ∃ u : rvObjectDomain U.object, u.val = x ∧ gammaVolumeValue U.toGammaRVObject u ∘ Fin.castAdd k = t := by
  change x ∈ (gammaVolumeSliceFormula U).graphSchema.rowDomain _ ↔ _
  rw [GammaRelationFormula.graphSchema_row_domain]
  constructor
  · rintro ⟨y,hy⟩
    obtain ⟨u,hu,hv⟩ := (gammaVolumeSliceSchema_volume U t x y).mp hy
    refine ⟨u,hu,?_⟩
    rw [hv]
    exact funext (fun j => Fin.append_left _ _ j)
  · rintro ⟨u,hu,hv⟩
    refine ⟨gammaVolumeValue U.toGammaRVObject u ∘ Fin.natAdd e,?_⟩
    apply (gammaVolumeSliceSchema_volume U t x _).mpr
    refine ⟨u,hu,?_⟩
    rw [← hv]
    exact Fin.append_castAdd_natAdd.symm

theorem gammaVolumeSliceSchema_finiteRows (U : GammaRVFiniteObject B (e+k))
    (t : Fin e → RV (M := M)) : (gammaVolumeSliceSchema U).finiteRow (fun j => (t j).val) := by
  refine ⟨?_,?_,?_⟩
  · intro x hx
    obtain ⟨y,hy⟩ := (GammaRelationFormula.graphSchema_row_domain (gammaVolumeSliceFormula U) _ x).mp hx
    refine ⟨y,hy,?_⟩
    intro z hz
    obtain ⟨u,hu,hy'⟩ := (gammaVolumeSliceSchema_volume U t x y).mp hy
    obtain ⟨v,hv,hz'⟩ := (gammaVolumeSliceSchema_volume U t x z).mp hz
    have he : v = u := Subtype.ext (hv.trans hu.symm)
    have hh : Fin.append t z = Fin.append t y := hz'.symm.trans ((congrArg (gammaVolumeValue U.toGammaRVObject) he).trans hy')
    funext j
    simpa only [Fin.append_right] using congrFun hh (Fin.natAdd e j)
  · intro x y hxy
    exact (GammaRelationFormula.graphSchema_row_domain (gammaVolumeSliceFormula U) _ x).mpr ⟨y,hxy⟩
  · intro y
    have h := (U.finite_volume ⟨Fin.append t y,Set.mem_univ _⟩).image (fun u : rvObjectDomain U.object => u.val)
    apply h.subset
    intro x hx
    obtain ⟨u,hu,hv⟩ := (gammaVolumeSliceSchema_volume U t x y).mp hx
    exact ⟨u,Subtype.ext hv,hu⟩

theorem gammaVolumeSliceSchema_value (U : GammaRVFiniteObject B (e+k)) (u : rvObjectDomain U.object) :
    (gammaVolumeSliceSchema U).rowValue
      (fun j => (gammaVolumeValue U.toGammaRVObject u (Fin.castAdd k j)).val) u.val =
        gammaVolumeValue U.toGammaRVObject u ∘ Fin.natAdd e := by
  let t := gammaVolumeValue U.toGammaRVObject u ∘ Fin.castAdd k
  have hx : u.val ∈ (gammaVolumeSliceSchema U).rowDomain (fun j => (t j).val) :=
    (gammaVolumeSliceSchema_domain U t u.val).mpr ⟨u,rfl,rfl⟩
  apply ((gammaVolumeSliceSchema U).rowValue_graph_of_finiteRow _ (gammaVolumeSliceSchema_finiteRows U t) _ hx _).mp
  exact (gammaVolumeSliceSchema_volume U t u.val _).mpr ⟨u,rfl,Fin.append_castAdd_natAdd.symm⟩

end IntegrationInACVF.Section6
