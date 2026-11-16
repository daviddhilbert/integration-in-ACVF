module

public import Integration7.CanonicalGammaVolumeIsomorphisms
public import Integration7.VolumeCoproduct
public import IntegrationSection6.FiniteGammaCoproducts

@[expose] public section

/-! Canonical transport of native tagged coproducts agrees with the
actual finite-volume coproduct, including its full coordinate map. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section5 (Point GammaGraphDefinable gammaLogicInput)
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {S : Set M} {k : ℕ}

theorem canonical_gamma_coprod_domain
    (hc : CanonicalStructure.IsCanonical (M := M))
    (U V : FiniteRV.GammaObjectAt B S (k+1)) :
    (canonicalFiniteRVObject hc (FiniteRV.gammaCoprodAt U V).object).obj.domain.carrier =
      (rvFiniteCoprodObject (canonicalFiniteRVObject hc U.object)
        (canonicalFiniteRVObject hc V.object)).obj.domain.carrier := by
  rfl

theorem canonical_gamma_coprod_object
    (hc : CanonicalStructure.IsCanonical (M := M))
    (U V : FiniteRV.GammaObjectAt B S (k+1)) :
    canonicalFiniteRVObject hc (FiniteRV.gammaCoprodAt U V).object =
      rvFiniteCoprodObject (canonicalFiniteRVObject hc U.object)
        (canonicalFiniteRVObject hc V.object) := by
  rfl

theorem canonical_gamma_coprod_volume_graph
    (hc : CanonicalStructure.IsCanonical (M := M))
    (U V : FiniteRV.GammaObjectAt B S (k+1))
    (ω : VolumeForm (canonicalFiniteRVObject hc U.object).obj.domain)
    (π : VolumeForm (canonicalFiniteRVObject hc V.object).obj.domain) :
    GammaGraphDefinable B
      (fun (p : Point (M := M) 0 (1+((canonicalFiniteRVObject hc U.object).obj.arity+
        (canonicalFiniteRVObject hc V.object).obj.arity)))
        (q : Point (M := M) 0 (k+1)) =>
        ((⟨canonicalFiniteRVObject hc U.object,ω⟩ : PositiveRVVolumeObject (M := M) S k).coprod
          (⟨canonicalFiniteRVObject hc V.object,π⟩ : PositiveRVVolumeObject (M := M) S k)).underlying.obj.volume.graph
            p.2 q.2) := canonical_gamma_object_volume_graph hc (FiniteRV.gammaCoprodAt U V)

theorem canonical_gamma_coprod_density_graph
    (hc : CanonicalStructure.IsCanonical (M := M))
    (U V : FiniteRV.GammaObjectAt B S (k+1))
    (ω : VolumeForm (canonicalFiniteRVObject hc U.object).obj.domain)
    (π : VolumeForm (canonicalFiniteRVObject hc V.object).obj.domain)
    (hω : GammaGraphDefinable B
      (fun (p : Point (M := M) 0 (canonicalFiniteRVObject hc U.object).obj.arity)
        (q : Point (M := M) 0 1) => ω.map.graph p.2 q.2))
    (hπ : GammaGraphDefinable B
      (fun (p : Point (M := M) 0 (canonicalFiniteRVObject hc V.object).obj.arity)
        (q : Point (M := M) 0 1) => π.map.graph p.2 q.2)) :
    GammaGraphDefinable B
      (fun (p : Point (M := M) 0 (1+((canonicalFiniteRVObject hc U.object).obj.arity+
        (canonicalFiniteRVObject hc V.object).obj.arity)))
        (q : Point (M := M) 0 1) =>
        ((⟨canonicalFiniteRVObject hc U.object,ω⟩ : PositiveRVVolumeObject (M := M) S k).coprod
          (⟨canonicalFiniteRVObject hc V.object,π⟩ : PositiveRVVolumeObject (M := M) S k)).form.map.graph
            p.2 q.2) := by
  let A : PositiveRVVolumeObject (M := M) S k := ⟨canonicalFiniteRVObject hc U.object,ω⟩
  let D : PositiveRVVolumeObject (M := M) S k := ⟨canonicalFiniteRVObject hc V.object,π⟩
  let L := gammaLogicInput B
  have hl := L.comp_graph (L.swap_graph
    (FiniteRV.gamma_leftTag_graph U (canonicalFiniteRVObject hc V.object).obj.arity)) hω
  have hr := L.comp_graph (L.swap_graph
    (FiniteRV.gamma_rightTag_graph V (canonicalFiniteRVObject hc U.object).obj.arity)) hπ
  apply GammaGraphDefinable.congr (L.union_graph hl hr)
  intro p q
  constructor
  · rintro (⟨z,⟨u,hu,htag⟩,⟨v,hv,hout⟩⟩ | ⟨z,⟨u,hu,htag⟩,⟨v,hv,hout⟩⟩)
    · let u' : A.underlying.obj.domain := ⟨u.val,u.property⟩
      have he : v = u' := Subtype.ext (hv.trans hu.symm)
      refine ⟨rvCoprodLeftMap A.underlying.obj D.underlying.obj u',htag,?_⟩
      funext j
      have hj : j = 0 := Subsingleton.elim _ _
      subst j
      change (A.coprod D).form.value _ = q.2 0
      rw [coprod_density_left]
      exact (congrArg (fun t => ω.value t) he).symm.trans (congrFun hout 0)
    · let u' : D.underlying.obj.domain := ⟨u.val,u.property⟩
      have he : v = u' := Subtype.ext (hv.trans hu.symm)
      refine ⟨rvCoprodRightMap A.underlying.obj D.underlying.obj u',htag,?_⟩
      funext j
      have hj : j = 0 := Subsingleton.elim _ _
      subst j
      change (A.coprod D).form.value _ = q.2 0
      rw [coprod_density_right]
      exact (congrArg (fun t => π.value t) he).symm.trans (congrFun hout 0)
  · rintro ⟨a,ha,hout⟩
    rcases a.property with ⟨u,hu⟩ | ⟨v,hv⟩
    · have he : a = rvCoprodLeftMap A.underlying.obj D.underlying.obj u := Subtype.ext hu.symm
      refine Or.inl ⟨(Fin.elim0,u.val),⟨⟨u.val,u.property⟩,rfl,hu.trans ha⟩,u,rfl,?_⟩
      funext j
      have hj : j = 0 := Subsingleton.elim _ _
      subst j
      have h := congrFun hout 0
      change (A.coprod D).form.value a = q.2 0 at h
      rw [he,coprod_density_left] at h
      exact h
    · have he : a = rvCoprodRightMap A.underlying.obj D.underlying.obj v := Subtype.ext hv.symm
      refine Or.inr ⟨(Fin.elim0,v.val),⟨⟨v.val,v.property⟩,rfl,hv.trans ha⟩,v,rfl,?_⟩
      funext j
      have hj : j = 0 := Subsingleton.elim _ _
      subst j
      have h := congrFun hout 0
      change (A.coprod D).form.value a = q.2 0 at h
      rw [he,coprod_density_right] at h
      exact h

end IntegrationInACVF.Section7
