module

public import Integration7.MixedJacobianOneOperations

@[expose] public section

/-! A finite RV family can be pulled across a Jacobian-one VF map.
Finite-fibre pullback keeps the same-base VF-small exceptional set small. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n a b c d : ℕ}

theorem VFAlmostEverywhere.pullback_finiteFibres
    {A : DefSet (rawMixedSpace (M := M) n a) S}
    {B : DefSet (rawMixedSpace (M := M) n b) S}
    (F : Map A B) (hF : F.FiniteFibres) {P : B → Prop}
    (hP : VFAlmostEverywhere B P) : VFAlmostEverywhere A (fun p => P (F p)) := by
  obtain ⟨D,hDB,hd,hP⟩ := hP
  let E : DefSet (rawMixedSpace (M := M) n a) S :=
    ⟨{x | ∃ p : A, p.val = x ∧ (F p).val ∈ D.carrier},F.definable_preimage D.definable⟩
  have hEA : E.carrier ⊆ A.carrier := by
    rintro x ⟨p,rfl,_⟩
    exact p.property
  let m : Map E D := (F.restrict hEA).corestrict (by
    intro x
    obtain ⟨p,he,hp⟩ := x.property
    have hx : (⟨x.val,hEA x.property⟩ : A) = p := Subtype.ext he.symm
    change (F (⟨x.val,hEA x.property⟩ : A)).val ∈ D.carrier
    rwa [hx])
  have hm : m.FiniteFibres := by
    intro v
    apply (hF ⟨v.val,hDB v.property⟩).of_injOn (f := fun x : E => (⟨x.val,hEA x.property⟩ : A))
    · intro x hx
      exact Subtype.ext (congrArg (fun z : D => z.val) hx)
    · intro x hx y hy he
      exact Subtype.ext (congrArg (fun z : A => z.val) he)
  refine ⟨E,hEA,(vfDim_le_of_finite_map _ m hm).trans_lt hd,?_⟩
  intro p hp
  exact hP (F p) (fun h => hp ⟨p,rfl,h⟩)

theorem vfJacobianOne_comp_finiteFibres
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) (hn : 0 < n)
    {A : DefSet (rawMixedSpace (M := M) n a) (C.base : Set M)}
    {B : DefSet (rawMixedSpace (M := M) n b) (C.base : Set M)}
    {D : DefSet (rawMixedSpace (M := M) n c) (C.base : Set M)}
    (f : Map A B) (g : Map B D) (hf : f.FiniteFibres)
    (hJf : VFAlmostEverywhere A (fun p => HasMixedVFJacobianAt f p 1))
    (hJg : VFAlmostEverywhere B (fun p => HasMixedVFJacobianAt g p 1)) :
    VFAlmostEverywhere A (fun p => HasMixedVFJacobianAt (g.comp f) p 1) := by
  letI : CharZero (VFType (M := M)) := Section6.vfCharZero_of_model00 C.model00
  obtain ⟨E,hEA,hd,hE⟩ := lemma_9_12_ae hc C.uncountable.le C.saturated C.small hn f g hf
  have hchain : VFAlmostEverywhere A (fun p => ∃ J K : VFType (M := M),
      HasMixedVFJacobianAt f p J ∧ HasMixedVFJacobianAt g (f p) K ∧
      HasMixedVFJacobianAt (g.comp f) p (K*J)) := ⟨E,hEA,hd,hE⟩
  have hboth := vfAlmostEverywhere_and hc C hJf (hJg.pullback_finiteFibres f hf)
  apply (vfAlmostEverywhere_and hc C hboth hchain).mono
  rintro p ⟨⟨hf,hg⟩,J,K,hJ,hK,hcomp⟩
  have h1 := hJ.unique hf
  have h2 := hK.unique hg
  simpa only [h1,h2,one_mul] using hcomp

theorem vfJacobianOne_of_finite_vf_projection
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) (hn : 0 < n)
    {A : DefSet (rawMixedSpace (M := M) n a) (C.base : Set M)}
    {B : DefSet (rawMixedSpace (M := M) n b) (C.base : Set M)}
    {D : DefSet (rawMixedSpace (M := M) n c) (C.base : Set M)}
    {E : DefSet (rawMixedSpace (M := M) n d) (C.base : Set M)}
    (q : Map A B) (g : Map B D) (f : Map A E) (hq : q.FiniteFibres)
    (hqVF : ∀ p, (q p).val.1 = p.val.1)
    (hVF : ∀ p, (g (q p)).val.1 = (f p).val.1)
    (hg : VFAlmostEverywhere B (fun p => HasMixedVFJacobianAt g p 1)) :
    VFAlmostEverywhere A (fun p => HasMixedVFJacobianAt f p 1) :=
  vfJacobianOne_of_same_vf hc C hn (g.comp q) f hVF
    (vfJacobianOne_comp_finiteFibres hc C hn q g hq
      (vfJacobianOne_of_preservesVF hc C hn q hqVF) hg)

end IntegrationInACVF.Section7
