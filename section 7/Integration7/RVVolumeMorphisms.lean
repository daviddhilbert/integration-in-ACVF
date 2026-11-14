import Integration7.RVVolumeObjects
import Section9.RVJacobian
import Section9.VolumeResidueCorrespondence

/-! The two volume equations on an essential finite-volume isomorphism.
The RV equation holds outside a definable set of smaller RV dimension;
the Gamma equation holds at every essential label. -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section9 SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {S : Set M} {a n k : ℕ}

def RVAlmostEverywhere (A : DefSet (rawRVSpace (M := M) a) S)
    (n : ℕ) (P : A → Prop) : Prop :=
  ∃ D : DefSet (rawRVSpace (M := M) a) S,
    D.carrier ⊆ A.carrier ∧ rvDim D < n ∧ ∀ u : A, u.val ∉ D.carrier → P u

omit [M ⊨ Axioms.ACVF] in
theorem RVAlmostEverywhere.mono {A : DefSet (rawRVSpace (M := M) a) S}
    {P Q : A → Prop} (h : RVAlmostEverywhere A n P) (hPQ : ∀ u, P u → Q u) :
    RVAlmostEverywhere A n Q := by
  obtain ⟨D, hDA, hd, hP⟩ := h
  exact ⟨D, hDA, hd, fun u hu => hPQ u (hP u hu)⟩

def finiteIsoMap {U V : RVFiniteObject (M := M) S n} (e : U ≅ V) :
    Map U.obj.domain V.obj.domain :=
  ((finiteVolumeProperty S n).ι.mapIso e).hom.map

def volumeRatio (U V : PositiveRVVolumeObject (M := M) S k)
    (e : U.essential ≅ V.essential) (u : U.essential.obj.domain) : CanonicalRV.RVSort M :=
  U.essentialForm.value u / V.essentialForm.value (finiteIsoMap e u)

structure RVVolumeIso (U V : PositiveRVVolumeObject (M := M) S k) where
  iso : U.essential ≅ V.essential
  gamma : ∀ u : U.essential.obj.domain,
    Values.vrv (U.essentialForm.value u) =
      Values.vrv (V.essentialForm.value (finiteIsoMap iso u)) *
        (rvGammaJacobian (U.essential.obj.value u)
          (V.essential.obj.value (finiteIsoMap iso u))
          (U.essential_nonzero u) (V.essential_nonzero (finiteIsoMap iso u))).val
  rv : RVAlmostEverywhere U.essential.obj.domain (k + 1) (fun u =>
    IsRVJacobianAt (volumeCorrespondence (finiteIsoMap iso)).carrier
      (U.essential.obj.value u) (V.essential.obj.value (finiteIsoMap iso u))
      (volumeRatio U V iso u))

def RVVolumeIsoInDegree (S : Set M) :
    (n : ℕ) → RVVolumeObject (M := M) S n → RVVolumeObject (M := M) S n → Type
  | 0, U, V => U ≅ V
  | _ + 1, U, V => RVVolumeIso U V

end IntegrationInACVF.Section7
