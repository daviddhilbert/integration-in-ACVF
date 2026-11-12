import IntegrationSection6.FiniteGammaWeightedIsos

/-! Isomorphism laws retain both real presentation maps and original-Gamma graphs. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
namespace IntegrationInACVF.Section6.FiniteRV
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

variable {B : Base (M := M)} {S : Set M} {n : ℕ}
local notation "N" => (@CanonicalStructure.normalize M sM)
local notation "hN" => (@CanonicalStructure.normalized_model M sM hM)

@[simp] theorem isoAtMap_inv_hom {U V : GammaObjectAt B S n} (e : U.object ≅ V.object)
    (u : rvObjectDomain U.object.obj) : isoAtMap e.symm (isoAtMap e u) = u := by
  exact @iso_hom_inv_apply M N hN S n U.object.obj V.object.obj (isoAtAmbient e) u

@[simp] theorem isoAtMap_hom_inv {U V : GammaObjectAt B S n} (e : U.object ≅ V.object)
    (v : rvObjectDomain V.object.obj) : isoAtMap e (isoAtMap e.symm v) = v := by
  exact @iso_inv_hom_apply M N hN S n U.object.obj V.object.obj (isoAtAmbient e) v

@[simp] theorem isoAtMap_trans {U V W : GammaObjectAt B S n}
    (e : U.object ≅ V.object) (f : V.object ≅ W.object) (u : rvObjectDomain U.object.obj) :
    isoAtMap (e.trans f) u = isoAtMap f (isoAtMap e u) := rfl

namespace GammaIsoAt

def refl (U : GammaObjectAt B S n) : GammaIsoAt U U where
  iso := Iso.refl U.object
  graph := (gammaIsoRefl U.toGamma).graph

def symm {U V : GammaObjectAt B S n} (e : GammaIsoAt U V) : GammaIsoAt V U where
  iso := e.iso.symm
  graph := by
    apply GammaGraphDefinable.congr ((gammaLogicInput B).swap_graph e.graph)
    intro q p
    constructor
    · rintro ⟨u,hu,he⟩
      exact ⟨isoAtMap e.iso u,he,by simpa only [isoAtMap_inv_hom] using hu⟩
    · rintro ⟨v,hv,hp⟩
      exact ⟨isoAtMap e.iso.symm v,hp,
        (congrArg (fun x : rvObjectDomain V.object.obj => x.val) (isoAtMap_hom_inv e.iso v)).trans hv⟩

def trans {U V W : GammaObjectAt B S n} (e : GammaIsoAt U V) (f : GammaIsoAt V W) : GammaIsoAt U W where
  iso := e.iso.trans f.iso
  graph := by
    apply GammaGraphDefinable.congr ((gammaLogicInput B).comp_graph e.graph f.graph)
    intro p q
    constructor
    · rintro ⟨z,⟨u,hu,hz⟩,⟨v,hv,hq⟩⟩
      have he : v = isoAtMap e.iso u := Subtype.ext (hv.trans hz.symm)
      refine ⟨u,hu,?_⟩
      rw [isoAtMap_trans]
      exact (congrArg (fun v => (isoAtMap f.iso v).val) he).symm.trans hq
    · rintro ⟨u,hu,hq⟩
      exact ⟨(Fin.elim0,(isoAtMap e.iso u).val),⟨u,hu,rfl⟩,⟨isoAtMap e.iso u,rfl,hq⟩⟩

end GammaIsoAt
end IntegrationInACVF.Section6.FiniteRV
