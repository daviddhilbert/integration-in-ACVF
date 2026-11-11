import IntegrationSection5.ChainAlgebra

noncomputable section
set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5

namespace IntegrationInACVF.Section5
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {S : Set M} {m l r s t u : ℕ}
variable {A : DefSet (M := M) S 1 m} {B : DefSet (M := M) S 1 l}
variable {A' : DefSet (M := M) S 1 r} {B' : DefSet (M := M) S 1 s}
variable {A'' : DefSet (M := M) S 1 t} {B'' : DefSet (M := M) S 1 u}

theorem unaryConjugate_comp (T : SpecialBijection A A') (V : SpecialBijection B B')
    (U : SpecialBijection A' A'') (W : SpecialBijection B' B'')
    (hTU : (T.chain.append U.chain).Alternating none)
    (hVW : (V.chain.append W.chain).Alternating none) (f : Map A B) :
    unaryConjugate (T.comp U hTU) (V.comp W hVW) f =
      unaryConjugate U W (unaryConjugate T V f) := by
  apply Map.ext
  intro a
  change (V.comp W hVW).toMap (f ((T.comp U hTU).inverseMap a)) = _
  rw [special_comp_inverse T U hTU,special_comp_apply V W hVW]
  rfl

end IntegrationInACVF.Section5
