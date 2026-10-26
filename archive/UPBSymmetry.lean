/-
  UPB Supplement: Agent Neutrality vs. Presupposition P2
  ======================================================
  `RepairedUPB.agent_symmetry_coercion` (P2) says: if x may coerce y, then y may
  coerce x. The informal Presupposition 2 in the discussion says something weaker:
  moral rules must be invariant under *relabeling* agents (no one is privileged
  by name). This file formalizes that weaker principle (`AgentNeutral`) and shows:

  1. `predator_neutral`: the rule "the stronger may coerce the weaker" is agent-neutral.
  2. `neutrality_does_not_imply_P2`: there is an agent-neutral rule satisfying
     P1, P3 and P4 in a world where it violates P2. So P2 is strictly stronger than
     agent neutrality, and the symmetry-route theorem (1A/1C) does not survive
     replacing P2 with neutrality.
  3. `bodily_non_aggression_without_P2`, `property_non_aggression_without_P2`:
     the bodily and property prohibitions still follow from P1 + P3 alone, via the
     jurisdiction route. P2 is only needed to forbid coercion over resources the
     victim has no jurisdiction over.
-/
import UPBProof

namespace UPB

/-! ## Relabelings and worlds -/

/-- A relabeling of agents: a bijection, given together with its inverse. -/
structure Relabel (Agent : Type) where
  fwd : Agent → Agent
  inv : Agent → Agent
  inv_fwd : ∀ x, inv (fwd x) = x
  fwd_inv : ∀ x, fwd (inv x) = x

namespace Relabel

theorem fwd_inj {Agent : Type} (σ : Relabel Agent) {x y : Agent}
    (h : σ.fwd x = σ.fwd y) : x = y := by
  have h' := congrArg σ.inv h
  rwa [σ.inv_fwd, σ.inv_fwd] at h'

theorem inv_inj {Agent : Type} (σ : Relabel Agent) {x y : Agent}
    (h : σ.inv x = σ.inv y) : x = y := by
  have h' := congrArg σ.fwd h
  rwa [σ.fwd_inv, σ.fwd_inv] at h'

theorem fwd_ne_iff {Agent : Type} (σ : Relabel Agent) (x y : Agent) :
    σ.fwd x ≠ σ.fwd y ↔ x ≠ y :=
  ⟨fun h e => h (e ▸ rfl), fun h e => h (σ.fwd_inj e)⟩

end Relabel

/-- Rename the agents in an act. Resources are left alone. -/
def Act.relabel {Agent Resource : Type} (f : Agent → Agent) :
    Act Agent Resource → Act Agent Resource
  | .UseOwn x r       => .UseOwn (f x) r
  | .Coerce x y r     => .Coerce (f x) (f y) r
  | .Defend y x r     => .Defend (f y) (f x) r
  | .AvoidableAct x i => .AvoidableAct (f x) i

/-- The morally relevant facts of a situation: who has jurisdiction over what,
    and a non-moral relation between agents (here, physical strength). -/
structure World (Agent Resource : Type) where
  J : JurisdictionModel Agent Resource
  Stronger : Agent → Agent → Prop

/-- Apply a relabeling to the facts: whatever was true of `x` is now true of `σ x`. -/
def World.relabel {Agent Resource : Type} (σ : Relabel Agent)
    (w : World Agent Resource) : World Agent Resource where
  J :=
    { body := fun x => w.J.body (σ.inv x)
      body_injective := fun _ _ h => σ.inv_inj (w.J.body_injective _ _ h)
      HasJurisdiction := fun x r => w.J.HasJurisdiction (σ.inv x) r
      self_sovereignty := fun x => w.J.self_sovereignty (σ.inv x)
      exclusive_jurisdiction := fun _ _ r hx hy =>
        σ.inv_inj (w.J.exclusive_jurisdiction _ _ r hx hy) }
  Stronger := fun x y => w.Stronger (σ.inv x) (σ.inv y)

/-- A moral rule assigns a norm system to every possible world. -/
abbrev Rule (Agent Resource : Type) := World Agent Resource → NormSystem Agent Resource

/-- AGENT NEUTRALITY (the informal Presupposition 2): renaming everyone, consistently
    in both the facts and the act, never changes the verdict. Verdicts may depend on
    what is true of agents, but not on who they are. -/
def AgentNeutral {Agent Resource : Type} (R : Rule Agent Resource) : Prop :=
  ∀ (σ : Relabel Agent) (w : World Agent Resource) (a : Act Agent Resource),
    (R (w.relabel σ)).Perm (a.relabel σ.fwd) ↔ (R w).Perm a

/-- `RepairedUPB` with P2 (`agent_symmetry_coercion`) removed. -/
structure UPBWithoutP2 {Agent Resource : Type}
    (N : NormSystem Agent Resource) (J : JurisdictionModel Agent Resource) : Prop where
  compossible : ∀ a₁ a₂ : Act Agent Resource,
      InConflict J a₁ a₂ → ¬ (N.Perm a₁ ∧ N.Perm a₂)
  rightful_use_perm : ∀ (y : Agent) (r : Resource),
      J.HasJurisdiction y r → N.Perm (Act.UseOwn y r)
  rightful_defend_perm : ∀ (x y : Agent) (r : Resource),
      x ≠ y → J.HasJurisdiction y r → N.Perm (Act.Defend y x r)
  avoidable_perm : ∀ (x : Agent) (id : Nat), N.Perm (Act.AvoidableAct x id)

/-! ## The predator rule -/

/-- Build a norm system from its permissions; obligations follow by duality. -/
def NormSystem.ofPerm {Agent Resource : Type} (P : Act Agent Resource → Prop) :
    NormSystem Agent Resource where
  Perm := P
  ObligRefrain a := ¬ P a
  deontic_duality _ := Iff.rfl

/-- "The stronger may seize from the weaker anything the weaker has no jurisdiction
    over." Everything else matches `NAPSystem`. -/
def Predator {Agent Resource : Type} : Rule Agent Resource := fun w =>
  NormSystem.ofPerm fun
    | .UseOwn x r       => w.J.HasJurisdiction x r
    | .Coerce x y r     => x ≠ y ∧ w.Stronger x y ∧ ¬ w.J.HasJurisdiction y r
    | .Defend y x r     => x ≠ y ∧ w.J.HasJurisdiction y r
    | .AvoidableAct _ _ => True

/-- RESULT 1: The predator rule is agent-neutral. It privileges no one by name;
    it refers only to facts (strength, jurisdiction). -/
theorem predator_neutral {Agent Resource : Type} :
    AgentNeutral (Predator (Agent := Agent) (Resource := Resource)) := by
  intro σ w a
  cases a <;>
    simp only [Predator, NormSystem.ofPerm, Act.relabel, World.relabel,
      σ.inv_fwd, σ.fwd_ne_iff]

/-- In any world where strength is asymmetric, the predator rule satisfies every
    presupposition of `RepairedUPB` except P2. -/
theorem predator_without_P2 {Agent Resource : Type} (w : World Agent Resource)
    (hasym : ∀ x y, w.Stronger x y → ¬ w.Stronger y x) :
    UPBWithoutP2 (Predator w) w.J where
  compossible a₁ a₂ h_conf := by
    intro ⟨h₁, h₂⟩
    cases h_conf with
    | mutual_coercion x y r _       => exact hasym x y h₁.2.1 h₂.2.1
    | coerce_vs_use _ _ _ _ hj      => exact h₁.2.2 hj
    | coerce_vs_defend _ _ _ _ hj   => exact h₁.2.2 hj
  rightful_use_perm _ _ hj := hj
  rightful_defend_perm _ _ _ hxy hj := ⟨hxy, hj⟩
  avoidable_perm _ _ := True.intro

/-- A two-agent world: `true` is stronger than `false`. Resources are the two
    bodies (`some b`) and one unowned resource (`none`). -/
def twoAgentWorld : World Bool (Option Bool) where
  J :=
    { body := some
      body_injective := fun _ _ h => Option.some.inj h
      HasJurisdiction := fun x r => r = some x
      self_sovereignty := fun _ => rfl
      exclusive_jurisdiction := fun _ _ _ hx hy => Option.some.inj (hx.symm.trans hy) }
  Stronger := fun x y => x = true ∧ y = false

/-- RESULT 2: Agent neutrality does not imply P2. There is an agent-neutral rule that
    satisfies P1, P3 and P4 in some world, permits the stronger agent to coerce the
    weaker over the unowned resource, and therefore is not a `RepairedUPB`. -/
theorem neutrality_does_not_imply_P2 :
    ∃ (R : Rule Bool (Option Bool)) (w : World Bool (Option Bool)),
      AgentNeutral R ∧ UPBWithoutP2 (R w) w.J ∧
      (R w).Perm (Act.Coerce true false none) ∧ ¬ RepairedUPB (R w) w.J := by
  have hperm : (Predator twoAgentWorld).Perm (Act.Coerce true false none) :=
    ⟨by decide, ⟨rfl, rfl⟩, fun (h : (none : Option Bool) = some false) => by cases h⟩
  refine ⟨Predator, twoAgentWorld, predator_neutral, ?_, hperm, ?_⟩
  · apply predator_without_P2
    intro x y hxy hyx
    have h : true = false := hxy.1.symm.trans hyx.2
    cases h
  · intro H
    exact no_perm_coerce_via_symmetry _ _ H true false none (by decide) hperm

/-! ## What survives without P2 -/

theorem no_perm_coerce_without_P2 {Agent Resource : Type}
    (N : NormSystem Agent Resource) (J : JurisdictionModel Agent Resource)
    (H : UPBWithoutP2 N J) (x y : Agent) (r : Resource) (hxy : x ≠ y)
    (hj : J.HasJurisdiction y r) :
    ¬ N.Perm (Act.Coerce x y r) := fun h_perm =>
  H.compossible _ _ (InConflict.coerce_vs_defend x y r hxy hj)
    ⟨h_perm, H.rightful_defend_perm x y r hxy hj⟩

/-- RESULT 3a: Theorem 2 (bodily non-aggression) holds without P2. -/
theorem bodily_non_aggression_without_P2 {Agent Resource : Type}
    (N : NormSystem Agent Resource) (J : JurisdictionModel Agent Resource)
    (H : UPBWithoutP2 N J) (x y : Agent) (hxy : x ≠ y) :
    N.ObligRefrain (Act.Coerce x y (J.body y)) ∧ N.Perm (Act.Defend y x (J.body y)) :=
  ⟨(N.deontic_duality _).mpr
      (no_perm_coerce_without_P2 N J H x y _ hxy (J.self_sovereignty y)),
    H.rightful_defend_perm x y _ hxy (J.self_sovereignty y)⟩

/-- RESULT 3b: Theorem 3 (property non-aggression) holds without P2. -/
theorem property_non_aggression_without_P2 {Agent Resource : Type}
    (N : NormSystem Agent Resource) (J : JurisdictionModel Agent Resource)
    (H : UPBWithoutP2 N J) (x y : Agent) (r : Resource) (hxy : x ≠ y)
    (hj : J.HasJurisdiction y r) :
    N.ObligRefrain (Act.Coerce x y r) ∧ N.Perm (Act.UseOwn y r) :=
  ⟨(N.deontic_duality _).mpr (no_perm_coerce_without_P2 N J H x y r hxy hj),
    H.rightful_use_perm y r hj⟩

end UPB

#print axioms UPB.predator_neutral
#print axioms UPB.neutrality_does_not_imply_P2
#print axioms UPB.bodily_non_aggression_without_P2
#print axioms UPB.property_non_aggression_without_P2
