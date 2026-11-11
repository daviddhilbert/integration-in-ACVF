import IntegrationSection2.ConcreteVolumeForms
import Section9.RVFiniteEssential
import Section9.VolumeResidueCorrespondence

/-! The two actual volume conditions for an essential RV isomorphism.
In degree zero the category is RV[0] and no volume equation is imposed.
For positive degree the RV equation is generic in the label domain,
whereas the Gamma equation is required at every essential label. -/

set_option backward.isDefEq.respectTransparency false

open Set Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry
open IntegrationInACVF.Section2.ConcreteVolumeForms

namespace IntegrationInACVF.Section2.ConcreteVolumeMorphisms

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {k : ℕ}
  {U V : RVFiniteObject (M := M) S k}

def RVCompatible (e : U ≅ V) (ω : RVForm U) (π : RVForm V) : Prop :=
  let E := (finiteVolumeProperty S k).ι.mapIso e
  ∃ D : DefSet (rawRVSpace (M := M) U.obj.arity) S,
    rvDim D < k ∧ ∀ u : U.obj.domain, u.val ∉ D.carrier →
      IsRVJacobianAt (volumeCorrespondence E.hom.map).carrier
        (U.obj.value u) (V.obj.value (E.hom.map u)) (value ω u / value π (E.hom.map u))

def GammaCompatible (e : U ≅ V) (ω : RVForm U) (π : RVForm V)
    (hU : ∀ u : U.obj.domain, ∀ i, (U.obj.value u i).val ≠ iRVZero)
    (hV : ∀ u : V.obj.domain, ∀ i, (V.obj.value u i).val ≠ iRVZero) : Prop :=
  let E := (finiteVolumeProperty S k).ι.mapIso e
  ∀ u : U.obj.domain, gammaValue ω u = gammaValue π (E.hom.map u) *
    rvGammaJacobian (U.obj.value u) (V.obj.value (E.hom.map u)) (hU u) (hV (E.hom.map u))

def IsVolumeIsomorphism (e : U ≅ V) (ω : RVForm U) (π : RVForm V)
    (hU : ∀ u : U.obj.domain, ∀ i, (U.obj.value u i).val ≠ iRVZero)
    (hV : ∀ u : V.obj.domain, ∀ i, (V.obj.value u i).val ≠ iRVZero) : Prop :=
  k = 0 ∨ (RVCompatible e ω π ∧ GammaCompatible e ω π hU hV)

noncomputable def essentialForm {j : ℕ} {W : RVFiniteObject (M := M) S (j+1)}
    (ω : RVForm W) : RVForm (rvFiniteEssential W) where
  map := ω.map.restrict (rvEssentialLabels_subset W.obj)
  nonzero u := ω.nonzero ⟨u.val,rvEssentialLabels_subset W.obj u.property⟩

theorem zero_arity {U V : RVFiniteObject (M := M) S 0} (e : U ≅ V)
    (ω : RVForm U) (π : RVForm V) :
    IsVolumeIsomorphism e ω π (fun _ i => Fin.elim0 i) (fun _ i => Fin.elim0 i) := Or.inl rfl

end IntegrationInACVF.Section2.ConcreteVolumeMorphisms
