module

public import Integration7.NativeVFPairImages
public import IntegrationSection5.HeadPreparation
public import IntegrationSection6.GammaPermutedFibrePresentations
public import IntegrationSection5.NaturalContractionGamma

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Products with a full RV class admit the actual identity preparation
in that coordinate. These are the first contractions of the translated
balanced cells. The arbitrary other factor is left as its genuine VF set. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M}

theorem rv_class_product_head_saturated
    (A : DefSet (M := M) S 2 0) (r : RV (M := M)) (E : Set (VF (M := M)))
    (hA : nativeVFPairDomain A = {x | rv x = r} ×ˢ E) : HeadSaturated (carrier A) := by
  intro p hp x hx
  have hp' := (mem_native_vf_pair_domain A p).mpr hp
  rw [hA] at hp'
  apply (mem_native_vf_pair_domain A (replace 0 p x)).mp
  rw [hA]
  change rv ((replace 0 p x).1 0) = r ∧ (replace 0 p x).1 1 ∈ E
  simpa only [replace,Function.update_self,Function.update_of_ne (by decide : (1 : Fin 2) ≠ 0)] using
    (show rv x = r ∧ p.1 1 ∈ E from ⟨hx.trans hp'.1,hp'.2⟩)

theorem product_rv_class_permuted_head_saturated
    (A : DefSet (M := M) S 2 0) (t : RV (M := M)) (D : Set (VF (M := M)))
    (hA : nativeVFPairDomain A = D ×ˢ {x | rv x = t}) :
    HeadSaturated (carrier (vfPermutationImage A (Equiv.swap 0 1))) := by
  apply rv_class_product_head_saturated _ t D
  ext z
  constructor
  · rintro ⟨p,hp,rfl⟩
    have hp' := (vfPermutationImage_row A (Equiv.swap 0 1) p.1 p.2).mp hp
    have hq := (mem_native_vf_pair_domain A (p.1 ∘ (Equiv.swap 0 1).symm,p.2)).mpr hp'
    rw [hA] at hq
    simpa [twoVFPointPairEquiv] using And.intro hq.2 hq.1
  · intro hz
    let p : Point (M := M) 2 0 := (![z.1,z.2],Fin.elim0)
    refine ⟨p,?_,rfl⟩
    apply (vfPermutationImage_row A (Equiv.swap 0 1) p.1 p.2).mpr
    apply (mem_native_vf_pair_domain A (p.1 ∘ (Equiv.swap 0 1).symm,p.2)).mp
    rw [hA]
    simpa [twoVFPointPairEquiv,p] using And.intro hz.2 hz.1

def saturatedIdentityHead (A : DefSet (M := M) S 2 0) (hA : HeadSaturated (carrier A)) :
    HeadPreparation A := ⟨0,A,Map.id A,specialRelative_id A 0,hA⟩

theorem gamma_saturated_identity_head
    {B : Base (M := M)} (A : DefSet (M := M) S 2 0)
    (hA : HeadSaturated (carrier A)) (hΓ : GammaSetDefinable B (carrier A)) :
    GammaGraphDefinable B (pointMapGraph (saturatedIdentityHead A hA).map) :=
  gamma_identity_graph A hΓ

end IntegrationInACVF.Section7
