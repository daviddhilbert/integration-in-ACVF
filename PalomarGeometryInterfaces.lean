module
public import Integration7.HKPrincipalVolumeKernel
public section

/-! Pointwise specifications of the existing geometric map constructors. -/
noncomputable section
open FirstOrder FirstOrder.Language
namespace SpecialTransformations.DefinableGeometry.Map
variable {L : Language} {M : Type} [L.Structure M]
variable {P Q : Space L M} {S : Set M}

theorem palomar_ofCodes_value (A : DefSet P S) (f : P.Carrier → Q.Carrier)
    (F : (P.Index → M) → Q.Index → M) (hF : S.DefinableMap L F)
    (hdom : ∀ c : P.domain, F c.val ∈ Q.domain)
    (hdecode : ∀ c : P.domain, Q.decode ⟨F c.val, hdom c⟩ = f (P.decode c))
    (a : A) : (ofCodes A f F hF hdom hdecode a).val = f a.val := rfl

theorem palomar_inverse_value {A : DefSet P S} {B : DefSet Q S}
    (f : Map A B) (hf : Function.Bijective f) (b : B) :
    inverse f hf b = (Equiv.ofBijective f hf).symm b := rfl

end SpecialTransformations.DefinableGeometry.Map
