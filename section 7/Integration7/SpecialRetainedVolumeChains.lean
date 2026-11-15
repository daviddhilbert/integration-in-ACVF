import Integration7.SpecialVolumeJacobians
import Integration7.MixedRetainedLabelVolumeForms
import Integration7.UnaryChainVolumeOperations
import IntegrationSection5.RelativeLabelPreservation

/-! Actual special preparations retain a nonzero density label and
give genuine volume data on their relatively unary factor chains. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section9
open SpecialTransformations.Section5
open IntegrationInACVF.Section5

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n a b : ℕ}

theorem special_retained_density_nonzero
    {A : DefSet (M := M) S (n+1) a} {B : DefSet (M := M) S (n+1) b}
    (T : SpecialBijection A B) (δ : Fin a) (hδ : ∀ p : A, (p.val.2 δ).val ≠ iRVZero)
    (q : B) : (q.val.2 (suffixIndex (special_chain_rvArity_le T.chain) δ)).val ≠ iRVZero := by
  obtain ⟨p,hp⟩ := T.bijective.surjective q
  have h := special_oldLabels T p δ
  rw [hp] at h
  exact (congrArg Subtype.val h) ▸ hδ p

def specialRetainedVolumeForm (hc : CanonicalStructure.IsCanonical (M := M))
    {A : DefSet (M := M) S (n+1) a} {B : DefSet (M := M) S (n+1) b}
    (T : SpecialBijection A B) (δ : Fin a) (hδ : ∀ p : A, (p.val.2 δ).val ≠ iRVZero) :
    VolumeForm (rawSpecialSet hc B) :=
  mixedRetainedLabelVolumeForm (rawSpecialSet hc B) (suffixIndex (special_chain_rvArity_le T.chain) δ)
    (fun p => special_retained_density_nonzero T δ hδ ⟨p.val,p.property⟩)

theorem special_unary_chain_volume_data
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {A : DefSet (M := M) (C.base : Set M) (n+1) a}
    {B : DefSet (M := M) (C.base : Set M) (n+1) b}
    (T : SpecialBijection A B) (ω : VolumeForm (rawSpecialSet hc A)) (π : VolumeForm (rawSpecialSet hc B))
    (hDensity : ∀ p, ω.value p = π.value ((rawSpecialMap hc T.toMap) p)) :
    unaryChainVolumeData hc (specialUnaryChain (Nat.zero_lt_succ n) T.chain) ω π := by
  apply unary_chain_volume_data_of_composite hc C (Nat.zero_lt_succ n)
  rw [specialUnaryChain_toMap]
  exact (special_preserves_volume hc C (Nat.zero_lt_succ n) T ω π hDensity).1

end IntegrationInACVF.Section7
