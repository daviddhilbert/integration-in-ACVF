module

public import Integration7.GammaVolumeRowAgreements
public import IntegrationSection6.GammaPreparedRowAgreements
public import IntegrationSection6.GammaPreparedIndexPresentation

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Prepared row agreement retains an original density coordinate.
The equation holds on every prepared RV index, using its actual preimage. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {S : Set M} {p l a k : ℕ}

theorem prepared_volume_density_rows
    (A : DefSet (M := M) S p 0) (Z : DefSet (M := M) S p l) (K : SpecialBijection A Z)
    (F : GammaRVVolumeSchema B p a k (fun _ => .vf))
    (G : GammaRVVolumeSchema B (p+l) a k (fun _ => .rv))
    (hRows : ∀ q : Z, GammaVolumeRowAgreement F (rawVFParameter (K.inverseMap q).val) G (rawPreparedKey q.val))
    (δ : Fin a)
    (hDensity : ∀ x : A, ∀ r w, F.rowDensity (rawVFParameter x.val) r w ↔
      r ∈ F.object.rowDomain (rawVFParameter x.val) ∧ w 0 = r δ) :
    ∀ s ∈ preparedKeyDomain Z, ∀ r w, G.rowDensity (rvValues s) r w ↔
      r ∈ G.object.rowDomain (rvValues s) ∧ w 0 = r δ := by
  rintro s ⟨q,rfl⟩ r w
  exact ((hRows q).density r w).symm.trans
    ((hDensity (K.inverseMap q) r w).trans
      (and_congr (Set.ext_iff.mp (hRows q).1.domains r) Iff.rfl))

end IntegrationInACVF.Section7
