/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.EtaleTheta.ModelAut
import Iut.EtaleTheta.RigidSystems

/-!
# Discrete rigidity for the mod `N` model environments ([EtTh], Cor. 2.19(ii); milestone (13))

The mod `M` environment induced by a mod `N` environment (`M ∣ N`, [EtTh], Def. 2.13(ii): "we
write `M_{N'}` for the mod `N'` mono-theta environment induced by `M`") is, for the abelian
environments of `CyclotomicRigidity.lean`, the quotient by `M·μ` (`Env.red`): `μ_N/M·μ_N = μ_M`.
It is functorial in isomorphisms (`Env.redIso`), and for the models
`red M (modelN N l) ≅ modelN M l`
(`redModel`).

**`discreteRigidity`** ([EtTh], Cor. 2.19(ii), for the geometric theta quotient): for a chain
`N₀ ∣ N₁ ∣ ⋯` of nonzero levels and `l ≠ 0`, every projective system `(E_n, E_{n+1}|_{N_n} ≅ E_n)`
of environments, levelwise isomorphic to the models `modelN N_n l`, is isomorphic to the natural
projective system of models. This instantiates `RigidSystems.Tower.discreteRigidity` with the
surjections `Aut(modelN N l) ↠ Upper` of finite kernel of `ModelAut.lean` (the analogue of [EtTh],
Cor. 2.18(iv)), which are compatible with the reductions (`toQuot_redAut`).
-/

namespace Iut.EtaleTheta

open CategoryTheory RigidSystems

universe u

namespace Env

/-! ### Reduction of environments -/

/-- The subgroup `e·μ` of an environment. -/
def redSub (e : ℕ) (E : Env.{u}) : AddSubgroup E.carrier where
  carrier := {x | ∃ y ∈ E.mu, x = e • y}
  add_mem' := by
    rintro _ _ ⟨y, hy, rfl⟩ ⟨y', hy', rfl⟩
    exact ⟨y + y', E.mu.add_mem hy hy', (smul_add e y y').symm⟩
  zero_mem' := ⟨0, E.mu.zero_mem, (smul_zero e).symm⟩
  neg_mem' := by
    rintro _ ⟨y, hy, rfl⟩
    exact ⟨-y, E.mu.neg_mem hy, (smul_neg e y).symm⟩

/-- Additive isomorphisms preserve the torsion. -/
lemma mem_mu_map {E E' : Env.{u}} (f : E.carrier ≃+ E'.carrier) {y : E.carrier}
    (hy : y ∈ E.mu) : f y ∈ E'.mu :=
  f.toAddMonoidHom.isOfFinAddOrder hy

lemma map_redSub (e : ℕ) {E E' : Env.{u}} (f : E.carrier ≃+ E'.carrier) :
    (redSub e E).map f.toAddMonoidHom = redSub e E' := by
  ext x
  constructor
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    exact ⟨f y, mem_mu_map f hy, by simp⟩
  · rintro ⟨w, hw, rfl⟩
    exact ⟨e • f.symm w, ⟨f.symm w, mem_mu_map f.symm hw, rfl⟩, by simp⟩

/-- The automorphism of the quotient induced by an additive isomorphism. -/
abbrev redMap (e : ℕ) {E E' : Env.{u}} (f : E.carrier ≃+ E'.carrier) :
    (E.carrier ⧸ redSub e E) ≃+ (E'.carrier ⧸ redSub e E') :=
  QuotientAddGroup.congr _ _ f (map_redSub e f)

lemma redMap_mk (e : ℕ) {E E' : Env.{u}} (f : E.carrier ≃+ E'.carrier) (x : E.carrier) :
    redMap e f (x : E.carrier ⧸ redSub e E) = (f x : E'.carrier ⧸ redSub e E') :=
  rfl

lemma redMap_ext {e : ℕ} {E E' : Env.{u}}
    {g h : (E.carrier ⧸ redSub e E) ≃+ (E'.carrier ⧸ redSub e E')}
    (H : ∀ x : E.carrier, g x = h x) : g = h :=
  AddEquiv.ext fun x => QuotientAddGroup.induction_on x H

/-- **The mod `e` environment induced by `E`**: the quotient by `e·μ`. -/
abbrev red (e : ℕ) (E : Env.{u}) : Env.{u} where
  carrier := E.carrier ⧸ redSub e E
  D := {γ' | ∃ γ ∈ E.D, γ' = redMap e γ}
  S := E.S.map (QuotientAddGroup.mk' _)

/-- **The reduction of an isomorphism of environments.** -/
def redIso (e : ℕ) {E E' : Env.{u}} (f : Iso E E') : Iso (red e E) (red e E') where
  e := redMap e f.e
  map_D γ'' := by
    constructor
    · rintro ⟨γ, hγ, rfl⟩
      refine ⟨f.e.trans (γ.trans f.e.symm), (f.map_D γ).1 hγ, redMap_ext fun x => ?_⟩
      apply (redMap e f.e).injective
      simp only [AddEquiv.trans_apply, AddEquiv.apply_symm_apply]
      change ((γ (f.e x) : E'.carrier) : E'.carrier ⧸ redSub e E') =
        ((f.e (f.e.symm (γ (f.e x))) : E'.carrier) : E'.carrier ⧸ redSub e E')
      rw [AddEquiv.apply_symm_apply]
    · rintro ⟨δ, hδ, hδ'⟩
      refine ⟨f.e.symm.trans (δ.trans f.e), ?_, ?_⟩
      · rw [f.map_D]
        convert hδ using 1
        ext x
        simp
      · apply redMap_ext
        intro x
        have h := DFunLike.congr_fun hδ' ((f.e.symm x : E.carrier) : E.carrier ⧸ redSub e E)
        have h1 : redMap e f.e ((f.e.symm x : E.carrier) : E.carrier ⧸ redSub e E) =
            (x : E'.carrier ⧸ redSub e E') := by
          change ((f.e (f.e.symm x) : E'.carrier) : E'.carrier ⧸ redSub e E') = _
          rw [AddEquiv.apply_symm_apply]
        rw [AddEquiv.trans_apply, AddEquiv.trans_apply, h1, AddEquiv.symm_apply_eq] at h
        rw [h]
        rfl
  map_S := by
    change (E.S.map (QuotientAddGroup.mk' _)).map (redMap e f.e).toAddMonoidHom =
      E'.S.map (QuotientAddGroup.mk' _)
    rw [← f.map_S, AddSubgroup.map_map, AddSubgroup.map_map]
    rfl

@[simp] lemma redIso_e_mk (e : ℕ) {E E' : Env.{u}} (f : Iso E E') (x : E.carrier) :
    (redIso e f).e (x : E.carrier ⧸ redSub e E) = (f.e x : E'.carrier ⧸ redSub e E') :=
  redMap_mk e f.e x

end Env

/-! ### The category of environments -/

/-- Environments, as a groupoid (morphisms: isomorphisms of environments). -/
def EnvCat : Type 1 := Env.{0}

instance : Category.{1} EnvCat where
  Hom E E' := ULift.{1} (Env.Iso (E : Env.{0}) E')
  id E := ⟨Env.Iso.refl (E : Env.{0})⟩
  comp f g := ⟨f.down.trans g.down⟩
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

/-- The reduction functor `M ↦ M_e`. -/
def redFunctor (e : ℕ) : EnvCat ⥤ EnvCat where
  obj E := Env.red e (E : Env.{0})
  map f := ⟨Env.redIso e f.down⟩
  map_id E := by
    apply ULift.ext
    apply Env.Iso.ext
    apply Env.redMap_ext
    intro x
    rfl
  map_comp f g := by
    apply ULift.ext
    apply Env.Iso.ext
    apply Env.redMap_ext
    intro x
    rfl

/-! ### The reductions of the models -/

section RedModel

variable {N N' : ℕ} [NeZero N] [NeZero N'] (h : N ∣ N') (l : ℤ)

/-- The reduction `ℤ/N' × ℤ² → ℤ/N × ℤ²`. -/
def redHom : ZMod N' × ℤ × ℤ →+ ZMod N × ℤ × ℤ :=
  (ZMod.castHom h (ZMod N)).toAddMonoidHom.prodMap (AddMonoidHom.id (ℤ × ℤ))

omit [NeZero N] [NeZero N'] in
lemma redHom_apply (x : ZMod N' × ℤ × ℤ) :
    redHom h x = (ZMod.castHom h (ZMod N) x.1, x.2) := rfl

omit [NeZero N'] in
include h in
lemma cast_val (y : ZMod N) : (ZMod.cast ((y.val : ℕ) : ZMod N') : ZMod N) = y := by
  rw [ZMod.cast_natCast h, ZMod.natCast_zmod_val]

omit [NeZero N'] in
lemma redHom_surjective : Function.Surjective (redHom h) := by
  rintro ⟨y, x⟩
  exact ⟨((y.val : ℕ), x), by rw [redHom_apply, ZMod.castHom_apply, cast_val h]⟩

omit [NeZero N] in
include h in
/-- `ZMod.cast m = 0` iff `m ∈ N·(ℤ/N')`. -/
lemma cast_eq_zero_iff (m : ZMod N') :
    (ZMod.cast m : ZMod N) = 0 ↔ ∃ m' : ZMod N', m = N • m' := by
  constructor
  · intro hm
    have : ((m.val : ℕ) : ZMod N) = 0 := by
      rw [← ZMod.cast_natCast h, ZMod.natCast_zmod_val]
      exact hm
    obtain ⟨t, ht⟩ := (ZMod.natCast_eq_zero_iff _ _).1 this
    refine ⟨(t : ZMod N'), ?_⟩
    rw [← ZMod.natCast_zmod_val m, ht, nsmul_eq_mul, Nat.cast_mul]
  · rintro ⟨m', rfl⟩
    rw [← ZMod.castHom_apply (h := h), map_nsmul, ZMod.castHom_apply, nsmul_eq_mul,
      ZMod.natCast_self, zero_mul]

lemma mu_modelN : (modelN N' l).mu = (AddMonoidHom.inl (ZMod N') (ℤ × ℤ)).range :=
  model_mu fun x => isOfFinAddOrder_of_finite x

omit [NeZero N] in
lemma redSub_modelN : Env.redSub N (modelN N' l) = (redHom h).ker := by
  ext ⟨m, c, a⟩
  rw [AddMonoidHom.mem_ker, redHom_apply, ZMod.castHom_apply]
  constructor
  · rintro ⟨y, hy, hx⟩
    rw [mu_modelN] at hy
    obtain ⟨m', rfl⟩ := hy
    simp only [AddMonoidHom.inl_apply, Prod.smul_mk, smul_zero, Prod.mk.injEq] at hx
    obtain ⟨rfl, rfl, rfl⟩ := hx
    rw [(cast_eq_zero_iff h _).2 ⟨m', rfl⟩]
    rfl
  · intro hx
    have hm : (ZMod.cast m : ZMod N) = 0 := congrArg Prod.fst hx
    have hc : c = 0 := congrArg (fun z : ZMod N × ℤ × ℤ => z.2.1) hx
    have ha : a = 0 := congrArg (fun z : ZMod N × ℤ × ℤ => z.2.2) hx
    obtain ⟨m', rfl⟩ := (cast_eq_zero_iff h m).1 hm
    subst hc ha
    refine ⟨(m', 0, 0), ?_, ?_⟩
    · rw [mu_modelN]
      exact ⟨m', rfl⟩
    · simp

/-- The isomorphism of groups `(ℤ/N' × ℤ²)/(N·μ) ≅ ℤ/N × ℤ²`. -/
noncomputable def redModelEquiv :
    (Env.red N (modelN N' l)).carrier ≃+ (modelN N l).carrier :=
  (QuotientAddGroup.quotientAddEquivOfEq (redSub_modelN h l)).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective _ (redHom_surjective h))

lemma redModelEquiv_mk (x : ZMod N' × ℤ × ℤ) :
    redModelEquiv h l (x : (Env.red N (modelN N' l)).carrier) = redHom h x := rfl

omit [NeZero N] [NeZero N'] in
lemma redHom_gammaK (k : ℤ) (x : ZMod N' × ℤ × ℤ) :
    redHom h (gammaK ℤ l (ZMod N') k x) = gammaK ℤ l (ZMod N) k (redHom h x) := rfl

omit [NeZero N] [NeZero N'] in
lemma redHom_thetaSection (x : ℤ × ℤ) :
    redHom h (thetaSection ℤ (ZMod N') (redN N') 0 x) =
      thetaSection ℤ (ZMod N) (redN N) 0 x := by
  rw [redHom_apply]
  simp [thetaSection, redN, map_neg, map_intCast]

lemma redModelEquiv_gammaK (k : ℤ) (z : (Env.red N (modelN N' l)).carrier) :
    redModelEquiv h l (Env.redMap N (gammaK ℤ l (ZMod N') k) z) =
      gammaK ℤ l (ZMod N) k (redModelEquiv h l z) := by
  induction z using QuotientAddGroup.induction_on with
  | H x => exact redHom_gammaK h l k x

/-- **The mod `N` environment induced by the mod `N'` model is the mod `N` model.** -/
noncomputable def redModel : Env.Iso (Env.red N (modelN N' l)) (modelN N l) where
  e := redModelEquiv h l
  map_D γ := by
    constructor
    · rintro ⟨k, rfl⟩
      refine ⟨gammaK ℤ l (ZMod N') k, ⟨k, rfl⟩, Env.redMap_ext fun x => ?_⟩
      rw [AddEquiv.trans_apply, AddEquiv.trans_apply, AddEquiv.symm_apply_eq,
        redModelEquiv_gammaK]
    · rintro ⟨γ', ⟨k, rfl⟩, hk⟩
      refine ⟨k, AddEquiv.ext fun y => ?_⟩
      obtain ⟨z, rfl⟩ := (redModelEquiv h l).surjective y
      have := DFunLike.congr_fun hk z
      rw [AddEquiv.trans_apply, AddEquiv.trans_apply, AddEquiv.symm_apply_eq] at this
      rw [this, redModelEquiv_gammaK]
  map_S := by
    change ((modelN N' l).S.map (QuotientAddGroup.mk' _)).map (redModelEquiv h l).toAddMonoidHom =
      (modelN N l).S
    rw [AddSubgroup.map_map]
    ext y
    simp only [AddSubgroup.mem_map, AddMonoidHom.mem_range, AddMonoidHom.coe_comp,
      Function.comp_apply, exists_exists_eq_and]
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x, (redHom_thetaSection h x).symm⟩
    · rintro ⟨x, rfl⟩
      exact ⟨x, redHom_thetaSection h x⟩

/-- **The reduction of an automorphism acts on `ℤ²` as the automorphism itself.** -/
lemma toQuot_redAut (f : Env.Iso (modelN N' l) (modelN N' l)) :
    toQuot ((redModel h l).symm.trans ((Env.redIso N f).trans (redModel h l))) = toQuot f := by
  apply Equiv.ext
  intro x
  have hs : (redModelEquiv h l).symm (0, x) =
      (((0, x) : ZMod N' × ℤ × ℤ) : (Env.red N (modelN N' l)).carrier) := by
    rw [AddEquiv.symm_apply_eq, redModelEquiv_mk, redHom_apply, map_zero]
  rw [toQuot_apply, toQuot_apply]
  change ((redModelEquiv h l) ((Env.redIso N f).e ((redModelEquiv h l).symm (0, x)))).2 = _
  rw [hs]
  rfl

end RedModel

/-! ### The tower of models and discrete rigidity -/

/-- The isomorphism in `EnvCat` given by an isomorphism of environments. -/
def envIso {E E' : Env.{0}} (f : Env.Iso E E') : @CategoryTheory.Iso EnvCat _ E E' where
  hom := ⟨f⟩
  inv := ⟨f.symm⟩
  hom_inv_id := ULift.ext _ _ (Env.Iso.ext (AddEquiv.ext fun x => f.e.symm_apply_apply x))
  inv_hom_id := ULift.ext _ _ (Env.Iso.ext (AddEquiv.ext fun x => f.e.apply_symm_apply x))

/-- **A chain of nonzero levels** `N₀ ∣ N₁ ∣ N₂ ∣ ⋯` (the index set `E` of [EtTh],
Cor. 2.19(ii)). -/
structure LevelChain where
  /-- The levels. -/
  N : ℕ → ℕ
  ne_zero : ∀ n, N n ≠ 0
  dvd : ∀ n, N n ∣ N (n + 1)

namespace LevelChain

variable (Ns : LevelChain) (l : ℤ)

instance (n : ℕ) : NeZero (Ns.N n) := ⟨Ns.ne_zero n⟩

/-- **The tower of mod `N_n` environments** with the reduction functors and the model
environments `modelN N_n l` (the natural projective system of models). -/
noncomputable def tower : Tower.{1} where
  C _ := EnvCat
  res n := redFunctor (Ns.N n)
  model n := (modelN (Ns.N n) l : Env.{0})
  β n := envIso (redModel (Ns.dvd n) l)

/-- Automorphisms in `EnvCat` are automorphisms of environments. -/
def autHom (n : ℕ) : Aut ((Ns.tower l).model n) →* Env.Iso (modelN (Ns.N n) l) (modelN (Ns.N n) l)
    where
  toFun a := a.hom.down
  map_one' := rfl
  map_mul' _ _ := rfl

lemma autHom_injective (n : ℕ) : Function.Injective (Ns.autHom l n) := by
  intro a b h
  apply Iso.ext
  exact ULift.ext _ _ h

/-- The surjection `Aut(modelN N_n l) ↠ Upper`. -/
noncomputable def toUpperAt (hl : l ≠ 0) (n : ℕ) : Aut ((Ns.tower l).model n) →* Upper :=
  (toUpper hl).comp (Ns.autHom l n)

lemma toUpperAt_surjective (hl : l ≠ 0) (n : ℕ) : Function.Surjective (Ns.toUpperAt l hl n) := by
  intro σ
  obtain ⟨f, rfl⟩ := toUpper_surjective (N := Ns.N n) hl σ
  exact ⟨envIso f, rfl⟩

lemma toUpperAt_autRes (hl : l ≠ 0) (n : ℕ) :
    (Ns.toUpperAt l hl n).comp ((Ns.tower l).autRes n) = Ns.toUpperAt l hl (n + 1) := by
  ext a : 1
  apply Subtype.ext
  change toQuot (Ns.autHom l n ((Ns.tower l).autRes n a)) = toQuot (Ns.autHom l (n + 1) a)
  exact toQuot_redAut (Ns.dvd n) l (a.hom.down)

instance finite_ker_toUpperAt (hl : l ≠ 0) (n : ℕ) : Finite (Ns.toUpperAt l hl n).ker := by
  have : Finite (toUpper (N := Ns.N n) hl).ker := finite_ker_toUpper hl
  refine Finite.of_injective
    (fun a : (Ns.toUpperAt l hl n).ker => (⟨Ns.autHom l n a, a.2⟩ : (toUpper (N := Ns.N n) hl).ker))
    fun a b h => Subtype.ext (Ns.autHom_injective l n (congrArg Subtype.val h))

/-- **Discrete rigidity** ([EtTh], Cor. 2.19(ii), for the geometric theta quotient): every
projective system of environments `E_n` (with isomorphisms `(E_{n+1})_{N_n} ≅ E_n`) which is
levelwise isomorphic to the mod `N_n` models is isomorphic to the natural projective system of
models. -/
theorem discreteRigidity (hl : l ≠ 0) (S : (Ns.tower l).System)
    (hS : ∀ n, Nonempty (S.X n ≅ (Ns.tower l).model n)) : S.IsoModel :=
  (Ns.tower l).discreteRigidity (Ns.toUpperAt l hl) (Ns.toUpperAt_surjective l hl)
    (Ns.toUpperAt_autRes l hl) (Ns.finite_ker_toUpperAt l hl) S hS

end LevelChain

end Iut.EtaleTheta
