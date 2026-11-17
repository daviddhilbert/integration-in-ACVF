module

public import Integration7.TermClosureDefinability
public import Section4.VFRealFibres
public import Section4.RVCoordinates

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Definable maps send definable singleton inputs to definable singleton
outputs. For the actual real VF and RV presentations, each output
coordinate is therefore definable over the named input tuple. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] {S : Set M} {n : ℕ}

theorem map_singleton_definable {P Q : Space LRV M}
    {A : DefSet P S} {B : DefSet Q S} (f : Map A B) (a : A)
    (ha : P.Definable S {a.val}) : Q.Definable S {(f a).val} := by
  have h := (((ha.left_relation P Q).inter P Q f.graph_definable).swap P Q).exists_right Q P
  have he : {y | ∃ x, x ∈ ({a.val} : Set P.Carrier) ∧
      ∃ u : A, u.val = x ∧ (f u).val = y} = {(f a).val} := by
    ext y
    constructor
    · rintro ⟨x,hx,u,hu,hy⟩
      have hux : u = a := Subtype.ext (hu.trans hx)
      exact hy.symm.trans (congrArg (fun z : A => (f z).val) hux)
    · intro hy
      exact ⟨a.val,rfl,a,rfl,hy.symm⟩
  rwa [he] at h

theorem raw_vf_singleton_preimage (x : Fin n → VFType (M := M)) :
    (rawVFSpace (M := M) n).preimage {x} = {vfValues x} := by
  ext z
  constructor
  · rintro ⟨hz,hx⟩
    change (rawVFSpace (M := M) n).decode ⟨z,hz⟩ = x at hx
    change z = vfValues x
    rw [←hx]
    exact (vfValues_decode (M := M) (n := n) ⟨z,hz⟩).symm
  · rintro rfl
    exact ⟨⟨x,rfl⟩,decode_vfValues x⟩

theorem raw_rv_singleton_preimage (x : Fin n → CanonicalRV.RVSort M) :
    (rawRVSpace (M := M) n).preimage {x} = {rvValues x} := by
  ext z
  constructor
  · rintro ⟨hz,hx⟩
    change (rawRVSpace (M := M) n).decode ⟨z,hz⟩ = x at hx
    change z = rvValues x
    rw [←hx]
    exact (rvValues_decode (M := M) (n := n) ⟨z,hz⟩).symm
  · rintro rfl
    exact ⟨⟨x,rfl⟩,decode_rvValues x⟩

theorem raw_vf_singleton_definable (x : Fin n → VFType (M := M))
    (hx : ∀ i, S.Definable₁ LRV {(x i).val}) : (rawVFSpace (M := M) n).Definable S {x} := by
  change S.Definable LRV _
  rw [raw_vf_singleton_preimage]
  have h : S.Definable LRV (⋂ i : Fin n, {z : Fin n → M | z i = (x i).val}) :=
    Set.definable_iInter_of_finite (fun i : Fin n => by
      have hi := (hx i).preimage_comp (fun _ : Fin 1 => i)
      exact hi)
  have he : ({vfValues x} : Set (Fin n → M)) = ⋂ i : Fin n, {z : Fin n → M | z i = (x i).val} := by
    ext z
    simp only [Set.mem_singleton_iff,Set.mem_iInter,Set.mem_ofPred_eq]
    exact funext_iff
  rwa [he]

theorem tuple_singleton_coordinate_definable {x : Fin n → M}
    (hx : S.Definable LRV {x}) (i : Fin n) : S.Definable₁ LRV {x i} := by
  change S.Definable LRV {z : Fin 1 → M | z 0 = x i}
  have h := hx.image_comp (fun _ : Fin 1 => i)
  convert h using 1
  ext z
  simp only [Set.image_singleton,Set.mem_singleton_iff,Set.mem_setOf_eq]
  constructor
  · intro hz
    funext j
    change z j = x i
    simpa only [Fin.fin_one_eq_zero] using hz
  · intro hz
    exact congrFun hz 0

theorem finite_volume_parameter_context_definable
    (C : BaseContext M) (F : Set M) (hF : F.Finite)
    (hDef : ∀ f ∈ F, (C.base : Set M).Definable₁ LRV {f}) :
    ∀ d ∈ ((finiteVolumeParameterContext C F hF).base : Set M),
      (C.base : Set M).Definable₁ LRV {d} := by
  intro d hd
  exact SpecialTransformations.DefinableConstants.eliminate_parameters _
    (fun c hc => hc.elim (fun h => Set.Definable.singleton_of_mem LRV h) (hDef c))
    (definable_singleton_mem_termClosure hd)

end IntegrationInACVF.Section7
