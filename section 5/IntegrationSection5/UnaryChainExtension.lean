import IntegrationSection5.GammaUnaryChain
import Section5.ParameterExtension

/-! Changing an internal real presentation retains all actual factors and
all original-Gamma graph certificates. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5 SpecialTransformations.Section3
namespace IntegrationInACVF.Section5
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {S R : Set M} {n m l : ℕ}
variable {A : DefSet (M := M) S n m} {B : DefSet (M := M) S n l}

def extendUnaryMap (f : Map A B) (hSR : S ⊆ R) : Map (extendBase A hSR) (extendBase B hSR) :=
  @SpecialTransformations.DefinableGeometry.Map.extend LRV M (@CanonicalStructure.normalize M sM)
    (pointSpace n m) (pointSpace n l) S R A B f hSR

namespace UnaryChain

def extendBase (hSR : S ⊆ R) {m l : ℕ} {A : DefSet (M := M) S n m} {B : DefSet (M := M) S n l} :
    UnaryChain S n A B → UnaryChain R n (SpecialTransformations.Section5.extendBase A hSR) (SpecialTransformations.Section5.extendBase B hSR)
  | .nil A => .nil (SpecialTransformations.Section5.extendBase A hSR)
  | .cons i f hf hi tail => .cons i (extendUnaryMap f hSR) hf hi (extendBase hSR tail)

theorem extendBase_val (T : UnaryChain S n A B) (hSR : S ⊆ R) (a : A) :
    ((T.extendBase hSR).toMap a).val = (T.toMap a).val := by
  induction T with
  | nil A => rfl
  | cons i f hf hi tail ih => exact ih (f a)

theorem extendBase_gamma {G : GammaParameters.Base (M := M)} (T : UnaryChain S n A B)
    (hSR : S ⊆ R) (hT : GammaUnaryChainDefinable G T) : GammaUnaryChainDefinable G (T.extendBase hSR) := by
  induction T with
  | nil A => exact hT
  | cons i f hf hi tail ih => exact ⟨hT.1,ih hT.2⟩

end UnaryChain
end IntegrationInACVF.Section5
