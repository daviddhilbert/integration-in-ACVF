import Integration7.RVVolumeMorphisms

/-! Uniform density-bearing presentations. The degree-zero object forgets
the density, in accordance with ordinary RV[0]. -/

noncomputable section

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section4

namespace IntegrationInACVF.Section7

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M}

structure RVVolumeData (S : Set M) (n : ℕ) where
  underlying : RVFiniteObject (M := M) S n
  form : VolumeForm underlying.obj.domain

def RVVolumeData.toObject : {n : ℕ} → RVVolumeData (M := M) S n → RVVolumeObject (M := M) S n
  | 0, D => D.underlying
  | _ + 1, D => ⟨D.underlying, D.form⟩

end IntegrationInACVF.Section7
