/-
  UPB Supplement: The Jurisdiction Route, Without a Symmetry Premise
  ==================================================================
  A revision of `archive/UPBProof.lean` that:

  * Drops P2 (`agent_symmetry_coercion`). See `archive/UPBSymmetry.lean` for why P2 is
    strictly stronger than agent neutrality.
  * Separates possession (`Holds`: who physically controls a resource) from
    jurisdiction (`HasJurisdiction`: who has rightful title to it).
  * Makes conflict purely physical: acts collide when they cannot both be carried
    out, whoever owns what. Moral facts enter only through the permission premises.
    The old `mutual_coercion` case is gone: "x takes r from y" and "y takes r from x"
    each presuppose the other party holds `r`, so they cannot occur at the same time.
  * Grounds all title in ONE normative principle: title comes only from first
    possession or from a voluntary transfer (gift or sale) by the current owner.
    Self-ownership, exclusivity of title, and acquisition of unowned things are
    derived from it plus physical facts, not assumed. Because title depends only on
    the history of first possessions and owners' transfers, no decree, vote, uniform
    or act of force can create or transfer it, and a non-owner cannot pass on title.
  * Treats the body as non-transferable (no voluntary slavery). This is a separate,
    clearly labeled premise (`body_inalienable`) that can be dropped.
  * Shows that the moral premises alone (compossibility plus owners' use) also rule
    out two people having title to the same thing.
  * Replaces the `Coerce`/`Defend` labeling with one `Take` act. Whether a taking
    is aggression or recovery is decided by jurisdiction, not by its label.
  * Models enforcement by third parties (universal enforcement with an owner's veto).
    Anyone may stop an ongoing aggression or recover stolen property on the owner's
    behalf unless the owner declines.
  * Models PROPORTIONALITY as an undefined term. Uses of force carry an abstract
    `Force`, and `Proportionate` is a relation with no definition. Defensive force
    is permitted only when proportionate. An aggressor loses standing to resist
    proportionate force from anyone entitled to stop them, but keeps it against
    excessive force. Every theorem holds for every meaning of "proportionate".

  Necessity (using no more force than needed) is deliberately NOT required.
-/

namespace UPB2

/-! ## Acts, norm systems, worlds -/

/-- Elementary interpersonal actions. `Force` is an abstract type of ways of using force.
    - `Use x r`: `x` uses resource `r`
    - `Take x y r`: `x` forcibly takes control of `r` from `y`
    - `Defend y x r`: `y` forcibly resists `x`'s attempt to take `r`
    - `Intervene z x y r f`: `z` uses force `f` against `x`'s body to stop `x` taking
      `r` from `y` (`z = y` is self-defense with force)
    - `Resist x z f`: `x` resists force `f` that `z` is using against `x`'s body
    - `AvoidableAct x id`: a non-invasive action others can freely avoid
    - `Strike z x f`: `z` uses force `f` against `x`'s body (assault; murder if `f` is
      lethal). Stopping an aggression is the separate act `Intervene`.
    - `Stop z a`: `z` uses force to stop the act `a` by whoever is doing it -/
inductive Act (Agent Resource Force : Type) where
  | Use          (x : Agent) (r : Resource) : Act Agent Resource Force
  | Take         (x y : Agent) (r : Resource) : Act Agent Resource Force
  | Defend       (y x : Agent) (r : Resource) : Act Agent Resource Force
  | Intervene    (z x y : Agent) (r : Resource) (f : Force) : Act Agent Resource Force
  | Resist       (x z : Agent) (f : Force) : Act Agent Resource Force
  | AvoidableAct (x : Agent) (id : Nat) : Act Agent Resource Force
  | Strike       (z x : Agent) (f : Force) : Act Agent Resource Force
  | Stop         (z : Agent) (a : Act Agent Resource Force) : Act Agent Resource Force

/-- Who does an act. -/
def Act.doer {Agent Resource Force : Type} : Act Agent Resource Force → Agent
  | .Use x _              => x
  | .Take x _ _           => x
  | .Defend y _ _         => y
  | .Intervene z _ _ _ _  => z
  | .Resist x _ _         => x
  | .AvoidableAct x _     => x
  | .Strike z _ _         => z
  | .Stop z _             => z

/-- A deontic norm system with the standard duality `ObligRefrain a ↔ ¬ Perm a`. -/
structure NormSystem (Agent Resource Force : Type) where
  Perm : Act Agent Resource Force → Prop
  ObligRefrain : Act Agent Resource Force → Prop
  deontic_duality : ∀ a : Act Agent Resource Force, ObligRefrain a ↔ ¬ Perm a

/-- Build a norm system from its permissions; obligations follow by duality. -/
def NormSystem.ofPerm {Agent Resource Force : Type}
    (P : Act Agent Resource Force → Prop) : NormSystem Agent Resource Force where
  Perm := P
  ObligRefrain a := ¬ P a
  deontic_duality _ := Iff.rfl

/-! ## Title over time -/

/-- The history of events that bear on title. Time is measured in steps `0, 1, 2, …`. -/
structure History (Agent Resource : Type) where
  /-- `FirstAt t x r`: at time `t`, `x` became the first person ever to possess `r`. -/
  FirstAt : Nat → Agent → Resource → Prop
  /-- `GaveAt t x y r`: at time `t`, `x` handed `r` over to `y` as a gift, sale or other
      transfer. A taking against `x`'s will is not a handing over. Whether the handover
      was voluntary is recorded separately, by `DeceivedAt` and `CoercedAt`. -/
  GaveAt : Nat → Agent → Agent → Resource → Prop
  /-- `DeceivedAt t x y r`: `x`'s handover of `r` to `y` at time `t` was induced by
      deception (fraud). -/
  DeceivedAt : Nat → Agent → Agent → Resource → Prop
  /-- `CoercedAt t x y r`: `x`'s handover of `r` to `y` at time `t` was made under threat
      of initiated force (duress). -/
  CoercedAt : Nat → Agent → Agent → Resource → Prop
  /-- `Alienable r`: title to `r` can be transferred. -/
  Alienable : Resource → Prop
  /-- UNDEFINED TERM. `Capable t x`: at time `t`, `x` is able to choose: not asleep, in a
      coma, too young, or otherwise lacking the capacity for responsible choice. Ages,
      thresholds and degrees are deliberately left undefined. -/
  Capable : Nat → Agent → Prop
  /-- RECORD OF WRONGS. `TookAt t x y r`: at time `t`, `x` took `r` from `y` by force. -/
  TookAt : Nat → Agent → Agent → Resource → Prop
  /-- `DestroyedAt t x r`: at time `t`, `x` destroyed or damaged `r`. -/
  DestroyedAt : Nat → Agent → Resource → Prop
  /-- `InjuredAt t x y`: at time `t`, `x` injured `y`, other than by permitted defense or
      enforcement. Whether past force was justified is recorded here rather than derived. -/
  InjuredAt : Nat → Agent → Agent → Prop
  /-- CONTRACTS. `AgreedAt t x y`: at time `t`, `x` agreed to a contract under which `x`
      will owe `y` something, now or later, possibly on conditions (a loan to be repaid, a
      sale, a deposit forfeited if `x` fails to deliver). Agreement can be explicit or by
      conduct, such as ordering a meal. Whether given conduct amounts to agreement is
      recorded, not derived. -/
  AgreedAt : Nat → Agent → Agent → Prop
  /-- `AgreementDeceivedAt t x y`: `x`'s agreement with `y` at `t` was induced by deception. -/
  AgreementDeceivedAt : Nat → Agent → Agent → Prop
  /-- `AgreementCoercedAt t x y`: `x`'s agreement with `y` at `t` was made under threat of
      initiated force. -/
  AgreementCoercedAt : Nat → Agent → Agent → Prop
  /-- UNDEFINED TERM. `Outstanding t x y`: at time `t`, `x` owes `y` a payment that is due
      and not yet made, whether as compensation for a wrong or under a contract. How much is
      owed, when it falls due, and when it counts as paid, is deliberately left undefined. -/
  Outstanding : Nat → Agent → Agent → Prop
  /-- UNDEFINED TERM. `CompensatesAt t x y r`: at time `t`, `r`, owned by `x`, is designated
      as part of a payment `x` owes `y`, as compensation or under a contract. Which things
      make up the payment is deliberately left undefined. -/
  CompensatesAt : Nat → Agent → Agent → Resource → Prop

namespace History
variable {Agent Resource : Type} (h : History Agent Resource)

/-- A VOLUNTARY TRANSFER: a handover not induced by deception, not made under threat of
    initiated force, and made by someone with the capacity to choose. -/
def ValidGift (t : Nat) (x y : Agent) (r : Resource) : Prop :=
  h.GaveAt t x y r ∧ ¬ h.DeceivedAt t x y r ∧ ¬ h.CoercedAt t x y r ∧ h.Capable t x

/-- A WRONG, under strict liability. Given who has title at time `t` (`T`), `z` wronged
    `x` at `t` if `z` took from `x` something `x` owned, destroyed or damaged something
    `x` owned, or injured `x`. No fault is required, and no excuse removes the wrong. -/
def Wronged (T : Agent → Resource → Prop) (t : Nat) (z x : Agent) : Prop :=
  z ≠ x ∧ ((∃ r, h.TookAt t z x r ∧ T x r) ∨ (∃ r, h.DestroyedAt t z r ∧ T x r) ∨
    h.InjuredAt t z x)

/-- A VALID CONTRACT: an agreement not induced by deception, not made under threat of
    initiated force, and made by someone with the capacity to choose. -/
def ValidAgreement (t : Nat) (x y : Agent) : Prop :=
  h.AgreedAt t x y ∧ ¬ h.AgreementDeceivedAt t x y ∧ ¬ h.AgreementCoercedAt t x y ∧
    h.Capable t x

/-- CONSENT REQUIRES CAPACITY: someone lacking the capacity to choose can make neither a
    voluntary transfer nor a valid contract. Children cannot enter contracts. -/
theorem consent_requires_capacity {t : Nat} {x y : Agent} {r : Resource}
    (hinc : ¬ h.Capable t x) : ¬ h.ValidGift t x y r ∧ ¬ h.ValidAgreement t x y :=
  ⟨fun ⟨_, _, _, hc⟩ => hinc hc, fun ⟨_, _, _, hc⟩ => hinc hc⟩

/-- THE SOURCES OF DEBT: `z` incurs a debt to `x` at `t` by wronging `x` or by validly
    agreeing to a contract with `x`. Breaking a contract is not itself a further wrong;
    any penalty for breach has to be part of the contract. -/
def Incurs (T : Agent → Resource → Prop) (t : Nat) (z x : Agent) : Prop :=
  h.Wronged T t z x ∨ h.ValidAgreement t z x

/-- `z` owes `r` to `x` at `t`: `z`'s debt to `x` is outstanding at `t`, and `r` is
    designated as part of the compensation. Because a debt stays outstanding until paid,
    compensation can come from property `z` acquires long after the wrong. -/
def Owes (t : Nat) (z x : Agent) (r : Resource) : Prop :=
  h.Outstanding t z x ∧ h.CompensatesAt t z x r

/-- `r` is owed by `z` to someone at `t`. -/
def Owed (t : Nat) (z : Agent) (r : Resource) : Prop :=
  ∃ y, y ≠ z ∧ h.Owes t z y r

/-- TITLE PASSES from `z` to `x` at `t` in exactly two ways: a voluntary transfer of
    something not owed to a victim, or restitution of an outstanding debt. A victim's claim
    takes priority over a gift made at the same moment. -/
def Transfers (t : Nat) (z x : Agent) (r : Resource) : Prop :=
  (h.ValidGift t z x r ∧ ¬ h.Owed t z r) ∨ h.Owes t z x r

/-- `x`'s claim against `z` is older than `y`'s, as of time `s`: `z` incurred a debt to `x`
    (by a wrong or a contract) at some time up to `s` that is earlier than every debt `z`
    incurred to `y` up to `s`. Used to state the first-in-time priority rule, which puts
    victims of wrongs and contract creditors in a single queue. -/
def OlderClaim (T : Nat → Agent → Resource → Prop) (s : Nat) (z x y : Agent) : Prop :=
  ∃ t, t ≤ s ∧ h.Incurs (T t) t z x ∧ ∀ t', t' ≤ s → h.Incurs (T t') t' z y → t < t'

/-- THE TITLE RULE. `TitleAt t x r`: `x` has title to `r` at time `t`. You have title at a
    time exactly when one of these holds:
    - you became the first possessor of `r` at that time;
    - you had title at the previous time, and title did not pass from you then; or
    - `r` is transferable, and at the previous time title passed to you from its owner,
      by voluntary transfer or as restitution of a debt the owner owed you.
    A transfer from someone without title passes no title, and neither does a transfer
    obtained by fraud or under duress. -/
def TitleAt : Nat → Agent → Resource → Prop
  | 0, x, r => h.FirstAt 0 x r
  | t + 1, x, r => h.FirstAt (t + 1) x r ∨
      (TitleAt t x r ∧ ¬ (h.Alienable r ∧ ∃ y, y ≠ x ∧ h.Transfers t x y r)) ∨
      (h.Alienable r ∧ ∃ z, z ≠ x ∧ TitleAt t z r ∧ h.Transfers t z x r)

/-- Title passes from an owner to at most one person at a time, given that an owner
    cannot hand one thing to two people at once and a thing compensates only one victim. -/
theorem transfers_unique
    (hgu : ∀ t z x y r, h.GaveAt t z x r → h.GaveAt t z y r → x = y)
    (hcu : ∀ t z x y r, h.CompensatesAt t z x r → h.CompensatesAt t z y r → x = y)
    {t : Nat} {z x y : Agent} {r : Resource}
    (hzx : z ≠ x) (hzy : z ≠ y) (hx : h.Transfers t z x r) (hy : h.Transfers t z y r) :
    x = y := by
  rcases hx with ⟨hgx, hnox⟩ | ⟨hwx, hcx⟩ <;> rcases hy with ⟨hgy, hnoy⟩ | ⟨hwy, hcy⟩
  · exact hgu _ _ _ _ _ hgx.1 hgy.1
  · exact absurd ⟨y, fun e => hzy e.symm, hwy, hcy⟩ hnox
  · exact absurd ⟨x, fun e => hzx e.symm, hwx, hcx⟩ hnoy
  · exact hcu _ _ _ _ _ hcx hcy

/-- STRICT LIABILITY: destroying or damaging what someone else owns wrongs them, whatever
    the reason. Breaking a stranger's window to save your own life is still a wrong. -/
theorem destruction_wrongs {T : Agent → Resource → Prop} {t : Nat} {z x : Agent}
    {r : Resource} (hzx : z ≠ x) (hd : h.DestroyedAt t z r) (hx : T x r) :
    h.Wronged T t z x :=
  ⟨hzx, Or.inr (Or.inl ⟨r, hd, hx⟩)⟩

/-- STRICT LIABILITY: taking from someone what they own wrongs them, whatever the reason.
    The book's starving man who steals an apple does wrong, though understandably, and
    "must justly accept the consequences": he owes restitution. -/
theorem taking_wrongs {T : Agent → Resource → Prop} {t : Nat} {z x : Agent}
    {r : Resource} (hzx : z ≠ x) (ht : h.TookAt t z x r) (hx : T x r) :
    h.Wronged T t z x :=
  ⟨hzx, Or.inl ⟨r, ht, hx⟩⟩

/-- RESTITUTION: while `z`'s debt to `x` is outstanding, whatever transferable property of
    `z`'s is designated as compensation becomes `x`'s at the next step. -/
theorem restitution_passes_title {t : Nat} {z x : Agent} {r : Resource}
    (hz : h.TitleAt t z r) (ha : h.Alienable r) (hzx : z ≠ x)
    (hout : h.Outstanding t z x) (hc : h.CompensatesAt t z x r) :
    h.TitleAt (t + 1) x r :=
  Or.inr (Or.inr ⟨ha, z, hzx, hz, Or.inr ⟨hout, hc⟩⟩)

/-- The first possessor has title at the moment of first possession. -/
theorem title_of_first {t : Nat} {x : Agent} {r : Resource} (hf : h.FirstAt t x r) :
    h.TitleAt t x r := by
  cases t with
  | zero => exact hf
  | succ t => exact Or.inl hf

/-- Every title traces back to a first possession. -/
theorem title_origin {r : Resource} :
    ∀ (t : Nat) (x : Agent), h.TitleAt t x r → ∃ s, s ≤ t ∧ ∃ z, h.FirstAt s z r := by
  intro t
  induction t with
  | zero => exact fun x hx => ⟨0, Nat.le_refl 0, x, hx⟩
  | succ t ih =>
    intro x hx
    rcases hx with hf | ⟨hk, _⟩ | ⟨_, z, _, hz, _⟩
    · exact ⟨t + 1, Nat.le_refl _, x, hf⟩
    · obtain ⟨s, hs, rest⟩ := ih x hk
      exact ⟨s, Nat.le_succ_of_le hs, rest⟩
    · obtain ⟨s, hs, rest⟩ := ih z hz
      exact ⟨s, Nat.le_succ_of_le hs, rest⟩

/-- Once anyone has title to something, someone always has title to it afterwards:
    title is kept or passed on, never lost. -/
theorem title_persists {s : Nat} {z : Agent} {r : Resource} (hz : h.TitleAt s z r) :
    ∀ t, s ≤ t → ∃ x, h.TitleAt t x r := by
  intro t
  induction t with
  | zero =>
    intro hst
    have : s = 0 := Nat.le_zero.mp hst
    subst this
    exact ⟨z, hz⟩
  | succ t ih =>
    intro hst
    rcases Nat.lt_or_eq_of_le hst with hlt | heq
    · obtain ⟨x, hx⟩ := ih (Nat.le_of_lt_succ hlt)
      by_cases hg : h.Alienable r ∧ ∃ y, y ≠ x ∧ h.Transfers t x y r
      · obtain ⟨ha, y, hyx, hgv⟩ := hg
        exact ⟨y, Or.inr (Or.inr ⟨ha, x, fun e => hyx e.symm, hx, hgv⟩)⟩
      · exact ⟨x, Or.inr (Or.inl ⟨hx, hg⟩)⟩
    · subst heq
      exact ⟨z, hz⟩

/-- Title to a non-transferable thing stays with its holder forever. -/
theorem title_persists_of_inalienable {s : Nat} {x : Agent} {r : Resource}
    (hna : ¬ h.Alienable r) (hx : h.TitleAt s x r) : ∀ t, s ≤ t → h.TitleAt t x r := by
  intro t
  induction t with
  | zero =>
    intro hst
    have : s = 0 := Nat.le_zero.mp hst
    subst this
    exact hx
  | succ t ih =>
    intro hst
    rcases Nat.lt_or_eq_of_le hst with hlt | heq
    · exact Or.inr (Or.inl ⟨ih (Nat.le_of_lt_succ hlt), fun ⟨ha, _⟩ => hna ha⟩)
    · subst heq
      exact hx

/-- Title is exclusive at every time, given that a thing has only one first possessor,
    an owner cannot hand the same thing to two people at once, and a thing compensates
    only one victim. -/
theorem title_exclusive
    (hfu : ∀ t t' x y r, h.FirstAt t x r → h.FirstAt t' y r → x = y ∧ t = t')
    (hgu : ∀ t z x y r, h.GaveAt t z x r → h.GaveAt t z y r → x = y)
    (hcu : ∀ t z x y r, h.CompensatesAt t z x r → h.CompensatesAt t z y r → x = y) :
    ∀ (t : Nat) (x y : Agent) (r : Resource), h.TitleAt t x r → h.TitleAt t y r → x = y := by
  intro t
  induction t with
  | zero => exact fun x y r hx hy => (hfu 0 0 x y r hx hy).1
  | succ t ih =>
    intro x y r hx hy
    -- Nobody can become the first possessor of something someone already has title to.
    have nf : ∀ z v, h.TitleAt t z r → ¬ h.FirstAt (t + 1) v r := fun z v hz hv => by
      obtain ⟨s, hs, u, hu⟩ := h.title_origin t z hz
      have := (hfu _ _ _ _ _ hv hu).2
      omega
    rcases hx with hfx | ⟨hkx, hnx⟩ | ⟨hax, zx, hzx, htx, hgx⟩ <;>
      rcases hy with hfy | ⟨hky, hny⟩ | ⟨hay, zy, hzy, hty, hgy⟩
    · exact (hfu _ _ _ _ _ hfx hfy).1
    · exact absurd hfx (nf y x hky)
    · exact absurd hfx (nf zy x hty)
    · exact absurd hfy (nf x y hkx)
    · exact ih x y r hkx hky
    · obtain rfl : zy = x := ih zy x r hty hkx
      exact absurd ⟨hay, y, fun e => hzy e.symm, hgy⟩ hnx
    · exact absurd hfy (nf zx y htx)
    · obtain rfl : zx = y := ih zx y r htx hky
      exact absurd ⟨hax, x, fun e => hzx e.symm, hgx⟩ hny
    · obtain rfl : zx = zy := ih zx zy r htx hty
      exact h.transfers_unique hgu hcu hzx hzy hgx hgy

/-- NEMO DAT (no one gives what they do not have): the only ways to gain title are to
    become a thing's first possessor, or to receive it from someone who has title to it,
    by voluntary transfer or as restitution for a wrong they did you. A thief's "sale"
    passes no title, and neither does a taking. -/
theorem only_ways_to_gain_title {t : Nat} {x : Agent} {r : Resource}
    (hnew : h.TitleAt (t + 1) x r) (hold : ¬ h.TitleAt t x r) :
    h.FirstAt (t + 1) x r ∨
      (h.Alienable r ∧ ∃ z, z ≠ x ∧ h.TitleAt t z r ∧ h.Transfers t z x r) := by
  rcases hnew with hf | ⟨hk, _⟩ | hg
  · exact Or.inl hf
  · exact absurd hk hold
  · exact Or.inr hg

/-- NO ONE CAN CONSENT FOR YOU: you keep title to what you own unless title passes from
    *you*, by your own voluntary transfer or to pay your own debt. Nothing anyone else
    does, signs, agrees or votes, including your parents, can transfer your property. -/
theorem others_cannot_transfer_your_title {t : Nat} {x : Agent} {r : Resource}
    (hx : h.TitleAt t x r) (hnone : ¬ ∃ y, y ≠ x ∧ h.Transfers t x y r) :
    h.TitleAt (t + 1) x r :=
  Or.inr (Or.inl ⟨hx, fun ⟨_, hy⟩ => hnone hy⟩)

/-- HARMING YOURSELF WRONGS NO ONE: no one can wrong themselves, so destroying your own
    property or injuring yourself creates no debt. -/
theorem no_wrong_to_oneself {T : Agent → Resource → Prop} {t : Nat} {x : Agent} :
    ¬ h.Wronged T t x x :=
  fun hw => hw.1 rfl

/-- FRAUD AND DURESS PASS NO TITLE: if an owner's handover was induced by deception or
    made under threat of initiated force, the owner still has title afterwards (unless
    the thing was owed to one of the owner's own victims at that moment). -/
theorem invalid_transfer_keeps_title
    (hgu : ∀ t z x y r, h.GaveAt t z x r → h.GaveAt t z y r → x = y)
    {t : Nat} {z x : Agent} {r : Resource} (hz : h.TitleAt t z r)
    (hg : h.GaveAt t z x r) (hbad : h.DeceivedAt t z x r ∨ h.CoercedAt t z x r)
    (hno : ¬ h.Owed t z r) :
    h.TitleAt (t + 1) z r :=
  Or.inr (Or.inl ⟨hz, fun ⟨_, y, hyz, ht⟩ => by
    rcases ht with ⟨⟨hgy, hnd, hnc, _⟩, _⟩ | howes
    · obtain rfl : x = y := hgu t z x y r hg hgy
      rcases hbad with hd | hc
      · exact hnd hd
      · exact hnc hc
    · exact hno ⟨y, hyz, howes⟩⟩)

/-- A HANDOVER BY SOMEONE LACKING CAPACITY PASSES NO TITLE: if an owner is unable to
    choose (a child, a sleepwalker), nothing they hand over leaves their ownership, and
    they still have title afterwards (unless the thing was owed to one of their own
    creditors). -/
theorem incapable_transfer_keeps_title
    {t : Nat} {z : Agent} {r : Resource} (hz : h.TitleAt t z r)
    (hinc : ¬ h.Capable t z) (hno : ¬ h.Owed t z r) :
    h.TitleAt (t + 1) z r :=
  Or.inr (Or.inl ⟨hz, fun ⟨_, y, hyz, ht⟩ => by
    rcases ht with ⟨⟨_, _, _, hc⟩, _⟩ | howes
    · exact hinc hc
    · exact hno ⟨y, hyz, howes⟩⟩)

end History

/-! ## Worlds -/

/-- The facts of a situation: bodies, rightful title, the history of first possessions
    and transfers, current physical control, ongoing attempts to take, owners' choices
    about enforcement, and which uses of force are proportionate. -/
structure World (Agent Resource Force : Type) where
  body : Agent → Resource
  body_injective : ∀ (x y : Agent), body x = body y → x = y
  /-- `HasJurisdiction x r`: `x` has rightful title to `r` now. -/
  HasJurisdiction : Agent → Resource → Prop
  /-- `Holds x r`: `x` currently has physical control of `r`. -/
  Holds : Agent → Resource → Prop
  /-- Past first possessions and voluntary transfers. -/
  hist : History Agent Resource
  /-- The present time. -/
  now : Nat
  /-- `Attempting x y r`: `x` is currently trying to take `r` from `y`. -/
  Attempting : Agent → Agent → Resource → Prop
  /-- `Declines y r`: owner `y` declines enforcement by others of their claim to `r`. -/
  Declines : Agent → Resource → Prop
  /-- `Permits o x r`: `o` currently permits `x` to use `r` (lending, renting, inviting a
      guest). A license to use, not a transfer of title. It counts only if `o` owns `r`. -/
  Permits : Agent → Agent → Resource → Prop
  /-- UNDEFINED TERM. `Guardian g c`: `g` currently has custody of `c`, a dependent such as
      a child. How guardianship arises (by birth, adoption or otherwise) is not specified. -/
  Guardian : Agent → Agent → Prop
  /-- UNDEFINED TERM. `Provides g c`: `g` is currently providing adequate care for `c`. -/
  Provides : Agent → Agent → Prop
  /-- UNDEFINED TERM. `Contest x y`: `x` and `y` are currently engaged in a contest they
      have both agreed to, such as a boxing match, a game or a sparring session. -/
  Contest : Agent → Agent → Prop
  /-- UNDEFINED TERM. `InScope x y a`: act `a` is within the scope of the contest `x` and
      `y` agreed to. Agreeing to box is not agreeing to be stabbed. -/
  InScope : Agent → Agent → Act Agent Resource Force → Prop
  /-- UNDEFINED TERM. `Proportionate f x y r`: force `f` is proportionate as a means of
      stopping `x`'s aggression against `y` over `r`. No definition is given; the theorems
      hold for every interpretation satisfying `proportionate_exists`. -/
  Proportionate : Force → Agent → Agent → Resource → Prop
  /-- P0 (TITLE FROM FIRST POSSESSION AND CONSENSUAL TRANSFER), the normative premise
      about title: you have title now exactly when the title rule `History.TitleAt`
      gives it to you. -/
  title_rule : ∀ (x : Agent) (r : Resource),
    HasJurisdiction x r ↔ hist.TitleAt now x r
  /-- P0b (INALIENABLE BODIES): title to a person's body cannot be transferred, so
      there is no voluntary slavery. Contested; dropping it would make self-ownership
      hold only for people who have not given their body away. -/
  body_inalienable : ∀ x : Agent, ¬ hist.Alienable (body x)
  /-- Physical: every agent controls their own body. -/
  holds_body : ∀ x : Agent, Holds x (body x)
  /-- Physical: every agent became the first possessor of their own body at some time
      up to now. -/
  body_first : ∀ x : Agent, ∃ t, t ≤ now ∧ hist.FirstAt t x (body x)
  /-- Physical: a thing has only one first possessor, at only one time. -/
  first_unique : ∀ (t t' : Nat) (x y : Agent) (r : Resource),
    hist.FirstAt t x r → hist.FirstAt t' y r → x = y ∧ t = t'
  /-- Physical: no one can hand the same thing to two different people at once. -/
  gave_unique : ∀ (t : Nat) (z x y : Agent) (r : Resource),
    hist.GaveAt t z x r → hist.GaveAt t z y r → x = y
  /-- About the undefined terms: a single thing compensates only one victim at a time. -/
  compensation_unique : ∀ (t : Nat) (z x y : Agent) (r : Resource),
    hist.CompensatesAt t z x r → hist.CompensatesAt t z y r → x = y
  /-- STRICT LIABILITY, part of P0: every wrong creates a debt to the victim. -/
  wrong_creates_debt : ∀ (t : Nat) (z x : Agent),
    hist.Wronged (fun a b => hist.TitleAt t a b) t z x → hist.Outstanding t z x
  /-- About the undefined terms: debts arise only from wrongs and valid contracts by the
      debtor themselves. -/
  debt_requires_source : ∀ (t : Nat) (z x : Agent), hist.Outstanding t z x →
    ∃ s, s ≤ t ∧ hist.Incurs (fun a b => hist.TitleAt s a b) s z x
  /-- About the undefined terms: once a debt arising from wrongs is paid off, it stays paid
      off unless the debtor wrongs the same person again. (Debts under a contract can fall
      due repeatedly, as with installments, so they are not covered.) -/
  paid_stays_paid : ∀ (s t : Nat) (z x : Agent), s ≤ t → ¬ hist.Outstanding s z x →
    (∀ u, u ≤ t → ¬ hist.ValidAgreement u z x) →
    (∀ u, s < u → u ≤ t → ¬ hist.Wronged (fun a b => hist.TitleAt u a b) u z x) →
    ¬ hist.Outstanding t z x
  /-- FIRST IN TIME, part of P0: a debtor's property can be designated as payment to one
      creditor only if every creditor with an older claim has been paid off. Victims of
      wrongs and contract creditors share one queue. -/
  first_in_time : ∀ (s : Nat) (z x y : Agent) (r : Resource),
    hist.CompensatesAt s z y r →
    hist.OlderClaim (fun t a b => hist.TitleAt t a b) s z x y → ¬ hist.Outstanding s z x
  /-- A scarce thing can be licensed for use to only one person at a time, since two
      people cannot use it at once. -/
  permits_unique : ∀ (o x y : Agent) (r : Resource), Permits o x r → Permits o y r → x = y
  /-- Physical: anything currently held was first possessed by someone, at some time
      up to now. -/
  held_has_first : ∀ (y : Agent) (r : Resource), Holds y r →
    ∃ t, t ≤ now ∧ ∃ z, hist.FirstAt t z r
  /-- Every attempted taking, and every case of a guardian keeping custody without
      providing care, can be met with some proportionate force. Without this,
      "proportionate" could mean nothing at all and the right of defense would be empty. -/
  proportionate_exists : ∀ (x y : Agent) (r : Resource),
    (Attempting x y r ∨ (r = body y ∧ Guardian x y ∧ ¬ Provides x y)) →
    ∃ f, Proportionate f x y r

namespace World
variable {Agent Resource Force : Type} (w : World Agent Resource Force)

/-- NEGLECT: `g` keeps custody of `c` without providing adequate care. -/
def Neglects (g c : Agent) : Prop :=
  g ≠ c ∧ w.Guardian g c ∧ ¬ w.Provides g c

/-- `x` is aggressing against `y` over `r` in one of two ways:
    - `x` is trying to take `r` from `y`, who owns and holds it; or
    - `x` is neglecting `y` while keeping custody of them. In the book's analogy, this is
      like a husband who locks his wife in the basement and lets her starve. -/
def Aggressing (x y : Agent) (r : Resource) : Prop :=
  (w.Attempting x y r ∧ x ≠ y ∧ w.HasJurisdiction y r ∧ w.Holds y r) ∨
    (r = w.body y ∧ w.Neglects x y)

/-- `z` is entitled to enforce `v`'s claim to `r`: `z` is `v`, or `v` has not declined
    enforcement by others while having the capacity to choose. Someone lacking capacity
    cannot veto help, and no guardian can veto on their behalf. -/
def EntitledToEnforce (z v : Agent) (r : Resource) : Prop :=
  z = v ∨ ¬ (w.Declines v r ∧ w.hist.Capable w.now v)

/-- Owner `o` has currently licensed `r` to someone else. -/
def Licensed (o : Agent) (r : Resource) : Prop :=
  ∃ x, x ≠ o ∧ w.Permits o x r

/-- AN AGREED CONTEST: acts `a₁` and `a₂` are moves in a contest their two doers have both
    agreed to, both within its scope, and both doers currently have the capacity to
    choose (consent requires capacity). -/
def AgreedContest (a₁ a₂ : Act Agent Resource Force) : Prop :=
  w.Contest a₁.doer a₂.doer ∧ w.hist.Capable w.now a₁.doer ∧ w.hist.Capable w.now a₂.doer ∧
    w.InScope a₁.doer a₂.doer a₁ ∧ w.InScope a₁.doer a₂.doer a₂

/-- If two people are not in an agreed contest, nothing they do is a move in one. -/
theorem no_agreed_contest {a₁ a₂ : Act Agent Resource Force}
    (h : ¬ w.Contest a₁.doer a₂.doer) : ¬ w.AgreedContest a₁ a₂ :=
  fun hc => h hc.1

/-- `x` is liable to force `f` from `z`: `x` is aggressing against someone whose claim
    `z` is entitled to enforce, and `f` is proportionate to stopping that aggression. -/
def Liable (x z : Agent) (f : Force) : Prop :=
  ∃ (v : Agent) (r : Resource),
    w.Aggressing x v r ∧ w.EntitledToEnforce z v r ∧ w.Proportionate f x v r

/-- Someone other than the owner is not entitled to enforce a claim the owner, while
    capable, has declined to have enforced. -/
theorem not_entitled {z v : Agent} {r : Resource} (hzv : z ≠ v) (hdec : w.Declines v r)
    (hcap : w.hist.Capable w.now v) : ¬ w.EntitledToEnforce z v r :=
  fun h => h.elim hzv fun hn => hn ⟨hdec, hcap⟩

/-- NO VETO WITHOUT CAPACITY: anyone may enforce the claims of someone who currently
    lacks the capacity to choose. -/
theorem anyone_may_help_incapable {z v : Agent} {r : Resource}
    (hinc : ¬ w.hist.Capable w.now v) : w.EntitledToEnforce z v r :=
  Or.inr fun ⟨_, hc⟩ => hinc hc

/-- PROVIDE OR RELINQUISH: a guardian who is not trying to take control of their ward's
    body is aggressing against the ward only if they keep custody without providing care.
    Providing care, or giving up custody, ends the aggression. -/
theorem provide_or_relinquish {g c : Agent} (hna : ¬ w.Attempting g c (w.body c))
    (hok : w.Provides g c ∨ ¬ w.Guardian g c) : ¬ w.Aggressing g c (w.body c) := by
  rintro (⟨hat, _⟩ | ⟨_, _, hgd, hnp⟩)
  · exact hna hat
  · rcases hok with hp | hng
    · exact hnp hp
    · exact hng hgd

/-! ### What follows from the title rule -/

/-- DERIVED (formerly assumed): self-ownership. Every agent has title to their own body. -/
theorem self_sovereignty (x : Agent) : w.HasJurisdiction x (w.body x) :=
  let ⟨_, ht, hf⟩ := w.body_first x
  (w.title_rule x _).mpr
    (w.hist.title_persists_of_inalienable (w.body_inalienable x)
      (w.hist.title_of_first hf) w.now ht)

/-- DERIVED (formerly assumed): exclusivity. Title to a thing belongs to at most one agent. -/
theorem exclusive_jurisdiction (x y : Agent) (r : Resource)
    (hx : w.HasJurisdiction x r) (hy : w.HasJurisdiction y r) : x = y :=
  w.hist.title_exclusive w.first_unique w.gave_unique w.compensation_unique w.now x y r
    ((w.title_rule x r).mp hx) ((w.title_rule y r).mp hy)

/-- Anything someone holds is owned by someone. -/
theorem someone_owns_held (y : Agent) (r : Resource) (hy : w.Holds y r) :
    ∃ z, w.HasJurisdiction z r :=
  let ⟨_, ht, _, hz⟩ := w.held_has_first y r hy
  let ⟨x, hx⟩ := w.hist.title_persists (w.hist.title_of_first hz) w.now ht
  ⟨x, (w.title_rule x r).mpr hx⟩

/-- DERIVED (formerly assumed): acquisition. Holding something nobody has title to gives
    the holder title to it. In fact the situation cannot arise: whatever is held was
    first possessed by someone, and that title has passed to someone. -/
theorem acquisition (y : Agent) (r : Resource) (hy : w.Holds y r)
    (h_none : ∀ z, ¬ w.HasJurisdiction z r) : w.HasJurisdiction y r :=
  let ⟨z, hz⟩ := w.someone_owns_held y r hy
  absurd hz (h_none z)

/-- NO TITLE BY DECREE OR FORCE: title depends only on the history of first possessions
    and owners' voluntary transfers. Two situations with the same history agree on title,
    however they differ in anything else: who holds what (so taking something by force
    transfers no title), who is trying to take what, who has declined help, and any
    decree, vote, election or uniform, none of which is a first possession or an owner's
    voluntary transfer. A self-written deed is a case: the book's would-be tax collector
    with "a handwritten note saying that you own the whole neighbourhood" owns nothing
    by it. -/
theorem title_depends_only_on_history (w' : World Agent Resource Force)
    (hh : w.hist = w'.hist) (hn : w.now = w'.now) (x : Agent) (r : Resource) :
    w.HasJurisdiction x r ↔ w'.HasJurisdiction x r := by
  rw [w.title_rule, w'.title_rule, hh, hn]

/-- FRAUD AND DURESS: if, at the previous step, an owner handed something over because of
    deception or under threat of initiated force, the owner still owns it now and the
    recipient does not. This covers money obtained by fraud and payments extracted by
    threats, including payments demanded by anyone in any role. (The proviso `hno` sets
    aside the case where the thing was also owed to a victim of `z`'s own wrong.) -/
theorem fraud_or_duress_victim_keeps_title {t : Nat} {z x : Agent} {r : Resource}
    (hnow : w.now = t + 1) (hz : w.hist.TitleAt t z r) (hg : w.hist.GaveAt t z x r)
    (hbad : w.hist.DeceivedAt t z x r ∨ w.hist.CoercedAt t z x r)
    (hno : ¬ w.hist.Owed t z r) (hzx : z ≠ x) :
    w.HasJurisdiction z r ∧ ¬ w.HasJurisdiction x r := by
  have hz' : w.HasJurisdiction z r := by
    rw [w.title_rule, hnow]
    exact w.hist.invalid_transfer_keeps_title w.gave_unique hz hg hbad hno
  exact ⟨hz', fun hx => hzx (w.exclusive_jurisdiction z x r hz' hx)⟩

/-- EVERY WRONG CREATES A DEBT: if `z` wronged `x` at time `t` (by taking or destroying
    what `x` owned, or injuring `x`), `z` owes `x` compensation from then on, until it is
    paid off. -/
theorem debt_after_wrong {t : Nat} {z x : Agent}
    (hw : w.hist.Wronged (fun a b => w.hist.TitleAt t a b) t z x) :
    w.hist.Outstanding t z x :=
  w.wrong_creates_debt t z x hw

/-- RESTITUTION: if, at the previous step, `z`'s debt to `x` was outstanding, then whatever
    transferable property of `z`'s was designated as compensation now belongs to `x`, and
    no longer to `z`. The property can have been acquired at any time after the wrong,
    so unpaid debts do not lapse. Only the wrongdoer's own property can be designated,
    and never anyone's body. -/
theorem restitution_owned {t : Nat} {z x : Agent} {r : Resource}
    (hnow : w.now = t + 1) (hz : w.hist.TitleAt t z r) (ha : w.hist.Alienable r)
    (hzx : z ≠ x) (hout : w.hist.Outstanding t z x) (hc : w.hist.CompensatesAt t z x r) :
    w.HasJurisdiction x r ∧ ¬ w.HasJurisdiction z r := by
  have hx : w.HasJurisdiction x r := by
    rw [w.title_rule, hnow]
    exact w.hist.restitution_passes_title hz ha hzx hout hc
  exact ⟨hx, fun hz' => hzx (w.exclusive_jurisdiction z x r hz' hx)⟩

/-- FIRST IN TIME: while a creditor with an older claim is still owed, none of the debtor's
    property can be designated as payment to a later creditor. This applies across victims
    of wrongs and contract creditors alike. -/
theorem earlier_victims_first {s : Nat} {z x y : Agent} {r : Resource}
    (hout : w.hist.Outstanding s z x)
    (holder : w.hist.OlderClaim (fun t a b => w.hist.TitleAt t a b) s z x y) :
    ¬ w.hist.CompensatesAt s z y r :=
  fun hc => w.first_in_time s z x y r hc holder hout

/-- NO RESTITUTION FROM BODIES: no one's body can ever pass to another as compensation or
    under a contract, because bodies are not transferable (P0b). Debts are paid from
    property only. In particular, a contract to subject yourself to someone else's control
    for life transfers nothing. -/
theorem no_restitution_from_body (x y : Agent) (hxy : x ≠ y) :
    ¬ w.HasJurisdiction y (w.body x) :=
  fun hy => hxy (w.exclusive_jurisdiction x y _ (w.self_sovereignty x) hy)

/-- ONLY YOU CAN OBLIGATE YOURSELF: if, up to time `t`, `z` has neither wronged `x` nor
    validly agreed to a contract with `x`, then `z` owes `x` nothing at `t`. So a contract
    obtained by fraud or under duress creates no debt, and neither does a contract that
    someone else (a parent, a representative, "society") agreed to in `z`'s name. -/
theorem no_debt_without_source {t : Nat} {z x : Agent}
    (hnone : ∀ s, s ≤ t → ¬ w.hist.Incurs (fun a b => w.hist.TitleAt s a b) s z x) :
    ¬ w.hist.Outstanding t z x :=
  fun hout =>
    let ⟨s, hs, hinc⟩ := w.debt_requires_source t z x hout
    hnone s hs hinc

/-- A CONTRACT OBTAINED BY FRAUD OR DURESS IS NOT A VALID CONTRACT. -/
theorem invalid_agreement {t : Nat} {z x : Agent}
    (hbad : w.hist.AgreementDeceivedAt t z x ∨ w.hist.AgreementCoercedAt t z x) :
    ¬ w.hist.ValidAgreement t z x := by
  intro ⟨_, hnd, hnc, _⟩
  rcases hbad with hd | hc
  · exact hnd hd
  · exact hnc hc

end World

/-- Physical conflict. No moral facts appear here.
    - Taking `r` from `y` collides with `y`'s use or defense of `r`, and with anyone's
      intervention to stop that taking, whenever `y` actually holds `r`.
    - Intervening against `x` with force `f` collides with `x` resisting that force.
    - Two different people cannot both use the same scarce thing at the same time.
    - Using force on someone's body collides with their resisting it.
    - Forcibly stopping someone's act collides with their performing it. -/
inductive InConflict {Agent Resource Force : Type} (w : World Agent Resource Force) :
    Act Agent Resource Force → Act Agent Resource Force → Prop where
  | use_vs_use (x y : Agent) (r : Resource) (hxy : x ≠ y) :
      InConflict w (Act.Use x r) (Act.Use y r)
  | take_vs_use (x y : Agent) (r : Resource) (hxy : x ≠ y) (hy : w.Holds y r) :
      InConflict w (Act.Take x y r) (Act.Use y r)
  | take_vs_defend (x y : Agent) (r : Resource) (hxy : x ≠ y) (hy : w.Holds y r) :
      InConflict w (Act.Take x y r) (Act.Defend y x r)
  | take_vs_intervene (x y z : Agent) (r : Resource) (f : Force)
      (hxy : x ≠ y) (hy : w.Holds y r) :
      InConflict w (Act.Take x y r) (Act.Intervene z x y r f)
  | intervene_vs_resist (z x y : Agent) (r : Resource) (f : Force) (hzx : z ≠ x) :
      InConflict w (Act.Intervene z x y r f) (Act.Resist x z f)
  | strike_vs_resist (z x : Agent) (f : Force) (hzx : z ≠ x) :
      InConflict w (Act.Strike z x f) (Act.Resist x z f)
  | stop_vs_act (z : Agent) (a : Act Agent Resource Force) (hz : z ≠ a.doer) :
      InConflict w (Act.Stop z a) a

/-- THE PRESUPPOSITIONS. There is no symmetry premise. Enforcement is governed by one
    standing principle: the owner of a claim, and anyone else unless the owner declines,
    may enforce it (P5a, P5b); no one else may (P5c). -/
structure JurisdictionUPB {Agent Resource Force : Type}
    (N : NormSystem Agent Resource Force) (w : World Agent Resource Force) : Prop where
  /-- P1 (Compossibility): two physically conflicting acts are never both permitted, unless
      they are moves in a contest both parties agreed to. Equivalently
      (`compossible_iff_decisive`): in every physical conflict not agreed to, at least one
      party is obliged to yield. Mutual combat, such as boxing, is therefore not forbidden
      by P1; nor does any premise permit it. -/
  compossible : ∀ a₁ a₂ : Act Agent Resource Force,
      InConflict w a₁ a₂ → ¬ w.AgreedContest a₁ a₂ → ¬ (N.Perm a₁ ∧ N.Perm a₂)
  /-- P3a: an owner may use what they own, unless they have currently licensed it to
      someone else. -/
  owner_use : ∀ (y : Agent) (r : Resource),
      w.HasJurisdiction y r → ¬ w.Licensed y r → N.Perm (Act.Use y r)
  /-- P3e (Licenses): someone the owner currently permits to use a thing may use it. -/
  licensed_use : ∀ (o x : Agent) (r : Resource),
      w.HasJurisdiction o r → x ≠ o → w.Permits o x r → N.Perm (Act.Use x r)
  /-- P3b: an owner may resist anyone else's attempt to take what they own. -/
  owner_defend : ∀ (x y : Agent) (r : Resource),
      x ≠ y → w.HasJurisdiction y r → N.Perm (Act.Defend y x r)
  /-- P3d (Bodily resistance, with LIABILITY): you may resist force used against your
      body, except proportionate force from someone entitled to stop your aggression. -/
  body_resist : ∀ (x z : Agent) (f : Force),
      x ≠ z → ¬ w.Liable x z f → N.Perm (Act.Resist x z f)
  /-- P5a (Enforcement, defense): anyone entitled to enforce the victim's claim may use
      proportionate force to stop an ongoing aggression. -/
  enforce_defense : ∀ (z x y : Agent) (r : Resource) (f : Force),
      z ≠ x → w.Aggressing x y r → w.EntitledToEnforce z y r →
      w.Proportionate f x y r → N.Perm (Act.Intervene z x y r f)
  /-- P5b (Enforcement, recovery): anyone entitled to enforce the owner's claim may take
      the resource back from a holder who is neither its owner nor someone the owner
      permits to use it. With the owner as enforcer, this is the owner recovering their
      own property. -/
  enforce_recovery : ∀ (z y o : Agent) (r : Resource),
      z ≠ y → o ≠ y → w.HasJurisdiction o r → ¬ w.Permits o y r →
      w.EntitledToEnforce z o r → N.Perm (Act.Take z y r)
  /-- P5c (Standing): someone not entitled to enforce a claim may not enforce it, whether
      by intervening to stop an aggression or by taking the resource from anyone. -/
  standing : ∀ (z v : Agent) (r : Resource), ¬ w.EntitledToEnforce z v r →
      (∀ x f, ¬ N.Perm (Act.Intervene z x v r f)) ∧
      (w.HasJurisdiction v r → ∀ y, ¬ N.Perm (Act.Take z y r))
  /-- P4: avoidable, non-invasive actions are permitted. -/
  avoidable_perm : ∀ (x : Agent) (id : Nat), N.Perm (Act.AvoidableAct x id)

/-! ## Theorems -/

section
variable {Agent Resource Force : Type} {N : NormSystem Agent Resource Force}
  {w : World Agent Resource Force}

/-- THEOREM 0 (The moral premises alone force exclusive title): even setting aside the
    physical facts about first possession, compossibility (P1) and owners' use (P3a)
    rule out two people having title to the same thing. If both did (and neither had
    licensed it out), each would be permitted to use it, and those uses physically
    conflict. -/
theorem premises_force_exclusivity (H : JurisdictionUPB N w) (x y : Agent) (r : Resource)
    (hx : w.HasJurisdiction x r) (hy : w.HasJurisdiction y r)
    (hlx : ¬ w.Licensed x r) (hly : ¬ w.Licensed y r) (hnc : ¬ w.Contest x y) : x = y :=
  Classical.byContradiction fun hxy =>
    H.compossible _ _ (InConflict.use_vs_use x y r hxy) (w.no_agreed_contest hnc)
      ⟨H.owner_use x r hx hlx, H.owner_use y r hy hly⟩

/-- Someone not currently aggressing against anyone is liable to no force at all. -/
theorem not_liable_of_peaceful {x : Agent} (hpeace : ∀ v r, ¬ w.Aggressing x v r)
    (z : Agent) (f : Force) : ¬ w.Liable x z f :=
  fun ⟨v, r, hag, _⟩ => hpeace v r hag

/-- THEOREM 1 (Non-aggression): no one may take a resource from its owner who holds it,
    outside a contest they have both agreed to. (Throughout, the hypothesis `hnc` says the
    two parties are not in an agreed contest, which is when P1 applies.) -/
theorem no_take_from_owner (H : JurisdictionUPB N w) (x y : Agent) (r : Resource)
    (hxy : x ≠ y) (hy : w.Holds y r) (hj : w.HasJurisdiction y r) (hnc : ¬ w.Contest x y) :
    N.ObligRefrain (Act.Take x y r) :=
  (N.deontic_duality _).mpr fun h_take =>
    H.compossible _ _ (InConflict.take_vs_defend x y r hxy hy) (w.no_agreed_contest hnc)
      ⟨h_take, H.owner_defend x y r hxy hj⟩

/-- THEOREM 2 (Bodily non-aggression): no one may take control of another person's
    body, and that person may resist. This now holds even for aggressors: stopping an
    aggressor is intervention with proportionate force, not taking control of them.
    Confinement is a case: the book's wife locked in the basement may resist her
    confinement, unlike a wife whose husband is merely unfaithful, who can simply leave. -/
theorem bodily_non_aggression (H : JurisdictionUPB N w) (x y : Agent) (hxy : x ≠ y)
    (hnc : ¬ w.Contest x y) :
    N.ObligRefrain (Act.Take x y (w.body y)) ∧ N.Perm (Act.Defend y x (w.body y)) :=
  ⟨no_take_from_owner H x y _ hxy (w.holds_body y) (w.self_sovereignty y) hnc,
    H.owner_defend x y _ hxy (w.self_sovereignty y)⟩

/-- THEOREM 2A (Peaceful people may resist any force): someone not aggressing may
    resist any force anyone uses against their body. -/
theorem peaceful_may_resist (H : JurisdictionUPB N w) (x z : Agent) (f : Force)
    (hxz : x ≠ z) (hpeace : ∀ v r, ¬ w.Aggressing x v r) :
    N.Perm (Act.Resist x z f) :=
  H.body_resist x z f hxz (not_liable_of_peaceful hpeace z f)

/-- THEOREM 3 (Property non-aggression): no one may take an owned resource from its
    owner who holds it, and the owner may use it (unless they have lent it out). -/
theorem property_non_aggression (H : JurisdictionUPB N w) (x y : Agent) (r : Resource)
    (hxy : x ≠ y) (hy : w.Holds y r) (hj : w.HasJurisdiction y r) (hl : ¬ w.Licensed y r)
    (hnc : ¬ w.Contest x y) :
    N.ObligRefrain (Act.Take x y r) ∧ N.Perm (Act.Use y r) :=
  ⟨no_take_from_owner H x y r hxy hy hj hnc, H.owner_use y r hj hl⟩

/-- THEOREM 3F (No trespass): no one may use a thing they don't own without the owner's
    permission. If the owner has lent it to someone else, that person's use conflicts with
    the trespasser's; otherwise the owner's own use does. Either way P1 forbids the
    trespass. -/
theorem no_trespass (H : JurisdictionUPB N w) (o x : Agent) (r : Resource)
    (ho : w.HasJurisdiction o r) (hxo : x ≠ o) (hnp : ¬ w.Permits o x r)
    (hnc : ∀ v, ¬ w.Contest x v) :
    N.ObligRefrain (Act.Use x r) := by
  refine (N.deontic_duality _).mpr fun h_use => ?_
  by_cases hl : w.Licensed o r
  · obtain ⟨x', hx'o, hp⟩ := hl
    have hxx' : x ≠ x' := fun e => hnp (e ▸ hp)
    exact H.compossible _ _ (InConflict.use_vs_use x x' r hxx') (w.no_agreed_contest (hnc x'))
      ⟨h_use, H.licensed_use o x' r ho hx'o hp⟩
  · exact H.compossible _ _ (InConflict.use_vs_use x o r hxo) (w.no_agreed_contest (hnc o))
      ⟨h_use, H.owner_use o r ho hl⟩

/-- THEOREM 3G (Licenses): someone the owner permits to use a thing may use it, and while
    the license lasts the owner yields: the owner's own use would conflict with it. -/
theorem licensed_use_and_owner_yields (H : JurisdictionUPB N w) (o x : Agent) (r : Resource)
    (ho : w.HasJurisdiction o r) (hxo : x ≠ o) (hp : w.Permits o x r)
    (hnc : ¬ w.Contest x o) :
    N.Perm (Act.Use x r) ∧ N.ObligRefrain (Act.Use o r) := by
  have h_lic := H.licensed_use o x r ho hxo hp
  refine ⟨h_lic, (N.deontic_duality _).mpr fun h_own => ?_⟩
  exact H.compossible _ _ (InConflict.use_vs_use x o r hxo) (w.no_agreed_contest hnc)
    ⟨h_lic, h_own⟩

/-- THEOREM 3A (The formerly unowned resource): if `y` holds `r` and no one other than
    `y` has title to it, no one may take `r` from `y`. Whatever is held is owned by
    someone, and that someone can only be `y`. No symmetry premise is needed. -/
theorem no_take_from_sole_claimant (H : JurisdictionUPB N w) (x y : Agent) (r : Resource)
    (hxy : x ≠ y) (hy : w.Holds y r)
    (h_sole : ∀ z, w.HasJurisdiction z r → z = y) (hnc : ¬ w.Contest x y) :
    N.ObligRefrain (Act.Take x y r) := by
  obtain ⟨z, hj⟩ := w.someone_owns_held y r hy
  rw [h_sole z hj] at hj
  exact no_take_from_owner H x y r hxy hy hj hnc

/-- THEOREM 3B (Recovery by the owner): an owner may take back what they own from
    whoever holds it without permission, and the holder may neither keep using it nor
    resist. -/
theorem recovery (H : JurisdictionUPB N w) (x y : Agent) (r : Resource)
    (hxy : x ≠ y) (hy : w.Holds y r) (hj : w.HasJurisdiction x r)
    (hnp : ¬ w.Permits x y r) (hnc : ¬ w.Contest x y) :
    N.Perm (Act.Take x y r) ∧ N.ObligRefrain (Act.Use y r) ∧
      N.ObligRefrain (Act.Defend y x r) := by
  have h_take := H.enforce_recovery x y x r hxy hxy hj hnp (Or.inl rfl)
  refine ⟨h_take, (N.deontic_duality _).mpr ?_, (N.deontic_duality _).mpr ?_⟩
  · exact fun h_use => H.compossible _ _ (InConflict.take_vs_use x y r hxy hy)
      (w.no_agreed_contest hnc) ⟨h_take, h_use⟩
  · exact fun h_def => H.compossible _ _ (InConflict.take_vs_defend x y r hxy hy)
      (w.no_agreed_contest hnc) ⟨h_take, h_def⟩

/-- THEOREM 3C (Third-party recovery): unless the owner declines, anyone may take
    stolen property back from a holder who is not its owner and has no permission to
    use it, and the holder may neither keep using it nor resist. -/
theorem third_party_recovery (H : JurisdictionUPB N w) (z y o : Agent) (r : Resource)
    (hzy : z ≠ y) (hoy : o ≠ y) (hy : w.Holds y r) (ho : w.HasJurisdiction o r)
    (hnp : ¬ w.Permits o y r) (hnd : ¬ w.Declines o r) (hnc : ¬ w.Contest z y) :
    N.Perm (Act.Take z y r) ∧ N.ObligRefrain (Act.Use y r) ∧
      N.ObligRefrain (Act.Defend y z r) := by
  have h_take := H.enforce_recovery z y o r hzy hoy ho hnp (Or.inr fun ⟨hd, _⟩ => hnd hd)
  refine ⟨h_take, (N.deontic_duality _).mpr ?_, (N.deontic_duality _).mpr ?_⟩
  · exact fun h_use => H.compossible _ _ (InConflict.take_vs_use z y r hzy hy)
      (w.no_agreed_contest hnc) ⟨h_take, h_use⟩
  · exact fun h_def => H.compossible _ _ (InConflict.take_vs_defend z y r hzy hy)
      (w.no_agreed_contest hnc) ⟨h_take, h_def⟩

/-- THEOREM 3D (A rescuer must return what they recover): once rescuer `z` holds the
    owner's property, the owner may take it back and `z` may neither keep using it
    nor resist. This is Theorem 3B applied to the rescuer. -/
theorem rescuer_must_return (H : JurisdictionUPB N w) (o z : Agent) (r : Resource)
    (hoz : o ≠ z) (hz : w.Holds z r) (ho : w.HasJurisdiction o r)
    (hnp : ¬ w.Permits o z r) (hnc : ¬ w.Contest o z) :
    N.Perm (Act.Take o z r) ∧ N.ObligRefrain (Act.Use z r) ∧
      N.ObligRefrain (Act.Defend z o r) :=
  recovery H o z r hoz hz ho hnp hnc

/-- THEOREM 3J (A borrower must return what they borrowed): once the owner's permission
    ends, the owner may take the thing back from the borrower, who may neither keep using
    it nor resist. Damage done to it while borrowed is a wrong (`History.destruction_wrongs`)
    and so creates a debt. The book: "if I borrow your lawnmower, I am obligated to bring
    it back in more or less the same state that it was when I borrowed it." -/
theorem borrower_must_return (H : JurisdictionUPB N w) (o b : Agent) (r : Resource)
    (hob : o ≠ b) (hb : w.Holds b r) (ho : w.HasJurisdiction o r)
    (hended : ¬ w.Permits o b r) (hnc : ¬ w.Contest o b) :
    N.Perm (Act.Take o b r) ∧ N.ObligRefrain (Act.Use b r) ∧
      N.ObligRefrain (Act.Defend b o r) :=
  recovery H o b r hob hb ho hended hnc

/-- THEOREM 3K (Consensual bodily contact is not assault): someone who permits another to
    use their body, such as a patient consenting to surgery, makes that use permitted.
    The book's surgeon "stabs" with a scalpel, but by consent, unlike the mugger. -/
theorem consensual_bodily_contact (H : JurisdictionUPB N w) (x z : Agent) (hzx : z ≠ x)
    (hp : w.Permits x z (w.body x)) : N.Perm (Act.Use z (w.body x)) :=
  H.licensed_use x z _ (w.self_sovereignty x) hzx hp

/-- THEOREM 3H (Recovery after fraud or duress): if, at the previous step, an owner
    handed something over because of deception or under threat of initiated force, the
    owner may now take it back from the recipient, who may neither keep using it nor
    resist. This applies to money extracted by threats in any role, including tax
    collection, unless a voluntary transfer occurred. -/
theorem fraud_or_duress_recovery (H : JurisdictionUPB N w) {t : Nat} (z x : Agent)
    (r : Resource) (hnow : w.now = t + 1) (hz : w.hist.TitleAt t z r)
    (hg : w.hist.GaveAt t z x r) (hbad : w.hist.DeceivedAt t z x r ∨ w.hist.CoercedAt t z x r)
    (hno : ¬ w.hist.Owed t z r)
    (hzx : z ≠ x) (hx : w.Holds x r) (hnp : ¬ w.Permits z x r) (hnc : ¬ w.Contest z x) :
    N.Perm (Act.Take z x r) ∧ N.ObligRefrain (Act.Use x r) ∧
      N.ObligRefrain (Act.Defend x z r) :=
  recovery H z x r hzx hx
    (w.fraud_or_duress_victim_keeps_title hnow hz hg hbad hno hzx).1 hnp hnc

/-- THEOREM 3I (Collecting a debt): if, at the previous step, `z` owed `x` a payment that was
    due, and some of `z`'s property was designated as payment, then `x` may take it from
    `z`, and `z` may neither keep using it nor resist. This covers compensation for wrongs
    and payments under contracts alike, such as repaying a loan, paying for a meal or
    forfeiting a deposit. Unless `x` declines, others may collect it on `x`'s behalf
    (Theorem 3C), using only proportionate force against `z`'s body. -/
theorem restitution_collection (H : JurisdictionUPB N w) {t : Nat} (z x : Agent)
    (r : Resource) (hnow : w.now = t + 1) (hz : w.hist.TitleAt t z r)
    (ha : w.hist.Alienable r) (hzx : z ≠ x) (hout : w.hist.Outstanding t z x)
    (hc : w.hist.CompensatesAt t z x r) (hhold : w.Holds z r) (hnp : ¬ w.Permits x z r)
    (hnc : ¬ w.Contest x z) :
    N.Perm (Act.Take x z r) ∧ N.ObligRefrain (Act.Use z r) ∧
      N.ObligRefrain (Act.Defend z x r) :=
  recovery H x z r (Ne.symm hzx) hhold (w.restitution_owned hnow hz ha hzx hout hc).1 hnp hnc

/-- THEOREM 3E (The owner's veto over recovery): if the owner, while capable, declines,
    no one else may take the resource from anyone. -/
theorem vetoed_recovery (H : JurisdictionUPB N w) (z y o : Agent) (r : Resource)
    (hzo : z ≠ o) (ho : w.HasJurisdiction o r) (hdec : w.Declines o r)
    (hcap : w.hist.Capable w.now o) :
    N.ObligRefrain (Act.Take z y r) :=
  (N.deontic_duality _).mpr ((H.standing z o r (w.not_entitled hzo hdec hcap)).2 ho y)

/-- THEOREM 4 (No exemptions): there is no agent at all, whatever their role or title,
    who may take an owned resource from its owner. This is Theorem 1 restated: it
    already quantifies over every agent, so no property of the taker can matter. It has
    teeth because of `World.title_depends_only_on_history`: a decree, vote or uniform
    cannot make the taker the owner, so the taking stays a taking from the owner unless
    the owner voluntarily transferred it. -/
theorem no_exemption (H : JurisdictionUPB N w) :
    ¬ ∃ (x y : Agent) (r : Resource), x ≠ y ∧ w.Holds y r ∧
      w.HasJurisdiction y r ∧ ¬ w.Contest x y ∧ N.Perm (Act.Take x y r) := by
  intro ⟨x, y, r, hxy, hy, hj, hnc, h_take⟩
  exact (N.deontic_duality _).mp (no_take_from_owner H x y r hxy hy hj hnc) h_take

/-- THEOREM 6 (Proportionate defense of others): unless the victim declines, anyone may
    use proportionate force to stop an ongoing aggression, and the aggressor may not
    resist it. With `z = y` this is self-defense, which needs no one's permission. -/
theorem defense_of_others (H : JurisdictionUPB N w) (z x y : Agent) (r : Resource)
    (f : Force) (hzx : z ≠ x) (hag : w.Aggressing x y r)
    (hent : w.EntitledToEnforce z y r) (hprop : w.Proportionate f x y r)
    (hnc : ¬ w.Contest z x) :
    N.Perm (Act.Intervene z x y r f) ∧ N.ObligRefrain (Act.Resist x z f) := by
  have h_int := H.enforce_defense z x y r f hzx hag hent hprop
  refine ⟨h_int, (N.deontic_duality _).mpr fun h_res => ?_⟩
  exact H.compossible _ _ (InConflict.intervene_vs_resist z x y r f hzx)
    (w.no_agreed_contest hnc) ⟨h_int, h_res⟩

/-- THEOREM 6A (Defense is always available): whenever an aggression is under way,
    anyone entitled to stop it has some permitted way of doing so. -/
theorem defense_available (H : JurisdictionUPB N w) (z x y : Agent) (r : Resource)
    (hzx : z ≠ x) (hag : w.Aggressing x y r) (hent : w.EntitledToEnforce z y r) :
    ∃ f, N.Perm (Act.Intervene z x y r f) :=
  have hcase : w.Attempting x y r ∨ (r = w.body y ∧ w.Guardian x y ∧ ¬ w.Provides x y) := by
    rcases hag with ⟨hat, _⟩ | ⟨hr, _, hgd, hnp⟩
    · exact Or.inl hat
    · exact Or.inr ⟨hr, hgd, hnp⟩
  let ⟨f, hprop⟩ := w.proportionate_exists x y r hcase
  ⟨f, H.enforce_defense z x y r f hzx hag hent hprop⟩

/-- THEOREM 6B (Excessive force is forbidden): if force `f` is not proportionate to any
    aggression by `x` that `z` is entitled to stop, then `z` may not use `f` against `x`,
    and `x` may resist it. This is derived, not assumed: it follows from `x`'s
    bodily resistance (P3d) and compossibility (P1). -/
theorem excessive_force_forbidden (H : JurisdictionUPB N w) (z x y : Agent) (r : Resource)
    (f : Force) (hzx : z ≠ x)
    (hexcess : ∀ v r', w.Aggressing x v r' → w.EntitledToEnforce z v r' →
      ¬ w.Proportionate f x v r') (hnc : ¬ w.Contest z x) :
    N.ObligRefrain (Act.Intervene z x y r f) ∧ N.Perm (Act.Resist x z f) := by
  have h_res : N.Perm (Act.Resist x z f) :=
    H.body_resist x z f (Ne.symm hzx) fun ⟨v, r', hag, hent, hprop⟩ =>
      hexcess v r' hag hent hprop
  refine ⟨(N.deontic_duality _).mpr fun h_int => ?_, h_res⟩
  exact H.compossible _ _ (InConflict.intervene_vs_resist z x y r f hzx)
    (w.no_agreed_contest hnc) ⟨h_int, h_res⟩

/-- THEOREM 6C (The victim's veto over defense): if the victim, while capable, declines,
    no one else may intervene on their behalf, with any force. -/
theorem vetoed_defense (H : JurisdictionUPB N w) (z x y : Agent) (r : Resource)
    (f : Force) (hzy : z ≠ y) (hdec : w.Declines y r) (hcap : w.hist.Capable w.now y) :
    N.ObligRefrain (Act.Intervene z x y r f) :=
  (N.deontic_duality _).mpr ((H.standing z y r (w.not_entitled hzy hdec hcap)).1 x f)

/-- THEOREM 13 (Rescue from neglect): if a guardian keeps custody of a child without
    providing care, anyone may use proportionate force to remove the child, and the
    guardian may not resist. The child, lacking capacity, cannot veto the rescue, and the
    guardian has no veto on the child's behalf. What may be enforced is "provide or
    relinquish": the guardian can end the aggression by providing care or giving up
    custody (`World.provide_or_relinquish`), and is never forced to work. Nothing here is
    specific to children: it covers any dependent lacking capacity, such as the residents
    of the book's nursing home. -/
theorem rescue_from_neglect (H : JurisdictionUPB N w) (z g c : Agent) (f : Force)
    (hzg : z ≠ g) (hneg : w.Neglects g c) (hinc : ¬ w.hist.Capable w.now c)
    (hprop : w.Proportionate f g c (w.body c)) (hnc : ¬ w.Contest z g) :
    N.Perm (Act.Intervene z g c (w.body c) f) ∧ N.ObligRefrain (Act.Resist g z f) :=
  defense_of_others H z g c _ f hzg (Or.inr ⟨rfl, hneg⟩) (w.anyone_may_help_incapable hinc)
    hprop hnc

/-- THEOREM 13A (Rescue is always possible): whenever a guardian is neglecting a child in
    their custody, anyone has some permitted way to remove the child. -/
theorem rescue_available (H : JurisdictionUPB N w) (z g c : Agent) (hzg : z ≠ g)
    (hneg : w.Neglects g c) (hinc : ¬ w.hist.Capable w.now c) :
    ∃ f, N.Perm (Act.Intervene z g c (w.body c) f) :=
  defense_available H z g c _ hzg (Or.inr ⟨rfl, hneg⟩) (w.anyone_may_help_incapable hinc)

/-- THEOREM 7 (No forcible prevention of permitted acts): no one may use force to stop
    someone else from doing what they are permitted to do. Derived from P1 alone: stopping
    an act physically conflicts with doing it. In particular, that forcing people to act
    "more practically" would be better for them is no justification (the book's
    *Practicality*). -/
theorem no_stopping_permitted_acts (H : JurisdictionUPB N w) (z : Agent)
    (a : Act Agent Resource Force) (hz : z ≠ a.doer) (ha : N.Perm a)
    (hnc : ¬ w.Contest z a.doer) :
    N.ObligRefrain (Act.Stop z a) :=
  (N.deontic_duality _).mpr fun h_stop =>
    H.compossible _ _ (InConflict.stop_vs_act z a hz) (w.no_agreed_contest hnc) ⟨h_stop, ha⟩

/-- THEOREM 7A (No force against avoidable acts): no one may use force to stop another
    person's avoidable, non-invasive act, such as rudeness, lateness or lying. This is the
    line between ethics and aesthetics in the book's *Ethics, Aesthetics and
    Avoidability*. Derived from P4 and Theorem 7. -/
theorem no_force_against_avoidable (H : JurisdictionUPB N w) (z x : Agent) (id : Nat)
    (hzx : z ≠ x) (hnc : ¬ w.Contest z x) :
    N.ObligRefrain (Act.Stop z (Act.AvoidableAct x id)) :=
  no_stopping_permitted_acts H z _ hzx (H.avoidable_perm x id) hnc

/-- THEOREM 7B (No victimless-crime enforcement): no one may use force to stop people
    using their own body or property, for example taking drugs, whatever the law says.
    Derived from owners' use (P3a) and Theorem 7. Combined with Theorem 8, this applies to
    police and officials as to anyone else. -/
theorem no_victimless_crime_enforcement (H : JurisdictionUPB N w) (z x : Agent)
    (r : Resource) (hzx : z ≠ x) (hj : w.HasJurisdiction x r) (hl : ¬ w.Licensed x r)
    (hnc : ¬ w.Contest z x) :
    N.ObligRefrain (Act.Stop z (Act.Use x r)) :=
  no_stopping_permitted_acts H z _ hzx (H.owner_use x r hj hl) hnc

/-- THEOREM 9 (Assault and murder): no one may use force against the body of someone who
    is not liable to that force, and the victim may resist. In particular no one may use
    any force, lethal or not, against a peaceful person. Derived from bodily resistance
    (P3d) and P1. -/
theorem no_assault (H : JurisdictionUPB N w) (z x : Agent) (f : Force) (hzx : z ≠ x)
    (hnl : ¬ w.Liable x z f) (hnc : ¬ w.Contest z x) :
    N.ObligRefrain (Act.Strike z x f) ∧ N.Perm (Act.Resist x z f) := by
  have h_res := H.body_resist x z f (Ne.symm hzx) hnl
  refine ⟨(N.deontic_duality _).mpr fun h_strike => ?_, h_res⟩
  exact H.compossible _ _ (InConflict.strike_vs_resist z x f hzx) (w.no_agreed_contest hnc)
    ⟨h_strike, h_res⟩

/-- THEOREM 9A (No assault or murder of peaceful people): Theorem 9 for someone who is
    not aggressing against anyone. -/
theorem no_assault_on_peaceful (H : JurisdictionUPB N w) (z x : Agent) (f : Force)
    (hzx : z ≠ x) (hpeace : ∀ v r, ¬ w.Aggressing x v r) (hnc : ¬ w.Contest z x) :
    N.ObligRefrain (Act.Strike z x f) ∧ N.Perm (Act.Resist x z f) :=
  no_assault H z x f hzx (not_liable_of_peaceful hpeace z f) hnc
/-- THEOREM 8 (No exemptions for roles, offices or majorities): let `Role` be any property
    of agents at all: holding an office, wearing a uniform, being in the majority of a
    vote. Everyone with that role is bound by the same prohibitions as everyone else:
    - they may not take an owned thing from its owner who holds it;
    - they may not strike or kill a peaceful person;
    - they may not forcibly stop anyone doing what they are permitted to do.
    `Role` plays no part in the proof, because no premise grants anything on the basis of
    who someone is. And by `World.title_depends_only_on_history`, no vote or decree can
    change who owns what. The same goes for authority claimed from God, "the government"
    or "the majority": a claimed command is just another role, and grants nothing. -/
theorem no_role_exemption (H : JurisdictionUPB N w) (Role : Agent → Prop) (z : Agent)
    (_ : Role z) :
    (∀ y r, z ≠ y → w.Holds y r → w.HasJurisdiction y r → ¬ w.Contest z y →
      N.ObligRefrain (Act.Take z y r)) ∧
    (∀ x f, z ≠ x → (∀ v r, ¬ w.Aggressing x v r) → ¬ w.Contest z x →
      N.ObligRefrain (Act.Strike z x f)) ∧
    (∀ a : Act Agent Resource Force, z ≠ a.doer → N.Perm a → ¬ w.Contest z a.doer →
      N.ObligRefrain (Act.Stop z a)) :=
  ⟨fun y r hzy hy hj hnc => no_take_from_owner H z y r hzy hy hj hnc,
   fun x f hzx hpeace hnc => (no_assault_on_peaceful H z x f hzx hpeace hnc).1,
   fun a hz ha hnc => no_stopping_permitted_acts H z a hz ha hnc⟩

/-- THEOREM 10 (Suicide and self-harm): no one may forcibly stop someone using their own
    body as they choose, including in ways that harm or end their own life. (The proviso
    is that they have not lent the use of their body to someone else.) -/
theorem no_stopping_self_harm (H : JurisdictionUPB N w) (z x : Agent) (hzx : z ≠ x)
    (hl : ¬ w.Licensed x (w.body x)) (hnc : ¬ w.Contest z x) :
    N.ObligRefrain (Act.Stop z (Act.Use x (w.body x))) :=
  no_victimless_crime_enforcement H z x _ hzx (w.self_sovereignty x) hl hnc

/-- THEOREM 11 (Freedom of association): let `id` be the avoidable act of declining to
    associate with someone: refusing to trade with them, befriend them, employ them or
    attend their school. No one may forcibly stop that refusal, and no one may take
    control of a person's body to force them into association. -/
theorem freedom_of_association (H : JurisdictionUPB N w) (z x : Agent) (id : Nat)
    (hzx : z ≠ x) (hnc : ¬ w.Contest z x) :
    N.ObligRefrain (Act.Stop z (Act.AvoidableAct x id)) ∧
      N.ObligRefrain (Act.Take z x (w.body x)) :=
  ⟨no_force_against_avoidable H z x id hzx hnc, (bodily_non_aggression H z x hzx hnc).1⟩

/-- CULPABILITY: `x` is culpable for act `a` if `x` does `a`, `a` is forbidden, and `x` is
    capable of choice now. This separates judging the *act* (permitted or forbidden) from
    judging the *agent* (to blame or not). -/
def Culpable (N : NormSystem Agent Resource Force) (w : World Agent Resource Force)
    (x : Agent) (a : Act Agent Resource Force) : Prop :=
  a.doer = x ∧ N.ObligRefrain a ∧ w.hist.Capable w.now x

/-- THEOREM 12 (No blame without capacity): no one is culpable for what they do while
    lacking the capacity to choose. A sleepwalker who steals isn't evil, even though
    stealing is forbidden. -/
theorem no_culpability_without_capacity {x : Agent} {a : Act Agent Resource Force}
    (hinc : ¬ w.hist.Capable w.now x) : ¬ Culpable N w x a :=
  fun ⟨_, _, hc⟩ => hinc hc

/-- THEOREM 12A (Innocent aggressors may be stopped): someone attacking while lacking
    capacity (a sleepwalker, a confused person) may still be stopped with proportionate
    force, and may not resist it. Liability depends on what someone is doing, not on
    their state of mind: "although we may restrain him." -/
theorem incapable_aggressor_may_be_stopped (H : JurisdictionUPB N w) (z x y : Agent)
    (r : Resource) (f : Force) (hzx : z ≠ x) (hag : w.Aggressing x y r)
    (hent : w.EntitledToEnforce z y r) (hprop : w.Proportionate f x y r)
    (_ : ¬ w.hist.Capable w.now x) (hnc : ¬ w.Contest z x) :
    N.Perm (Act.Intervene z x y r f) ∧ N.ObligRefrain (Act.Resist x z f) :=
  defense_of_others H z x y r f hzx hag hent hprop hnc

/-- THEOREM 12B (Those lacking capacity keep their rights): children, people in comas
    and others lacking capacity cannot be culpable, but they can be wronged. No one may
    take control of their body, and they keep title to it. -/
theorem incapable_keep_rights (H : JurisdictionUPB N w) (x y : Agent) (hxy : x ≠ y)
    (_ : ¬ w.hist.Capable w.now y) (hnc : ¬ w.Contest x y) :
    N.ObligRefrain (Act.Take x y (w.body y)) ∧ w.HasJurisdiction y (w.body y) :=
  ⟨(bodily_non_aggression H x y hxy hnc).1, w.self_sovereignty y⟩

/-- P1 RESTATED: "two conflicting acts are never both permitted" is equivalent to "at
    least one of them is forbidden", i.e. in every conflict someone must yield. -/
theorem compossible_iff_decisive (M : NormSystem Agent Resource Force)
    (a₁ a₂ : Act Agent Resource Force) :
    ¬ (M.Perm a₁ ∧ M.Perm a₂) ↔ (M.ObligRefrain a₁ ∨ M.ObligRefrain a₂) := by
  rw [M.deontic_duality a₁, M.deontic_duality a₂]
  constructor
  · intro h
    by_cases h1 : M.Perm a₁
    · exact Or.inr fun h2 => h ⟨h1, h2⟩
    · exact Or.inl h1
  · rintro (h | h) ⟨p1, p2⟩
    · exact h p1
    · exact h p2

end

/-! ## Consistency -/

/-- The canonical norm system for these presuppositions. -/
def JSystem {Agent Resource Force : Type} (w : World Agent Resource Force)
    (boxing : Prop := False) : NormSystem Agent Resource Force :=
  NormSystem.ofPerm fun
    | .Use x r             => (w.HasJurisdiction x r ∧ ¬ w.Licensed x r) ∨
        (∃ o, w.HasJurisdiction o r ∧ x ≠ o ∧ w.Permits o x r)
    | .Take x y r          => x ≠ y ∧ ((w.HasJurisdiction x r ∧ ¬ w.Permits x y r) ∨
        (¬ w.HasJurisdiction y r ∧
          ∃ o, w.HasJurisdiction o r ∧ ¬ w.Permits o y r ∧
            ¬ (w.Declines o r ∧ w.hist.Capable w.now o)))
    | .Defend y x r        => x ≠ y ∧ w.HasJurisdiction y r
    | .Intervene z x y r f => z ≠ x ∧ w.Aggressing x y r ∧ w.EntitledToEnforce z y r ∧
        w.Proportionate f x y r
    | .Resist x z f        => x ≠ z ∧ ¬ w.Liable x z f
    | .AvoidableAct _ _    => True
    | .Strike z x f        => boxing ∧ z ≠ x ∧
        w.AgreedContest (Act.Strike z x f) (Act.Resist x z f)
    | .Stop _ _            => False

/-- THEOREM 5 (Consistency): for every world, and so for every interpretation of the
    undefined terms, `JSystem` satisfies every presupposition. This holds whether or not
    `boxing` is switched on, i.e. whether strikes within an agreed contest are permitted
    or forbidden. -/
theorem consistent {Agent Resource Force : Type} (w : World Agent Resource Force)
    (boxing : Prop := False) : JurisdictionUPB (JSystem w boxing) w where
  compossible a₁ a₂ h_conf hnag := by
    intro ⟨h₁, h₂⟩
    cases h_conf with
    | use_vs_use x y r hxy =>
      rcases h₁ with ⟨hx, hlx⟩ | ⟨o, ho, hxo, hpx⟩ <;>
        rcases h₂ with ⟨hy, hly⟩ | ⟨o', ho', hyo', hpy⟩
      · exact hxy (w.exclusive_jurisdiction x y r hx hy)
      · have e := w.exclusive_jurisdiction o' x r ho' hx
        subst e
        exact hlx ⟨y, hyo', hpy⟩
      · have e := w.exclusive_jurisdiction o y r ho hy
        subst e
        exact hly ⟨x, hxo, hpx⟩
      · have e := w.exclusive_jurisdiction o o' r ho ho'
        subst e
        exact hxy (w.permits_unique o x y r hpx hpy)
    | take_vs_use x y r hxy _ =>
      rcases h₁.2 with ⟨hx, hnp⟩ | ⟨hny, o, ho, hnpo, _⟩ <;>
        rcases h₂ with ⟨hy, _⟩ | ⟨o', ho', _, hpy⟩
      · exact hxy (w.exclusive_jurisdiction x y r hx hy)
      · have e := w.exclusive_jurisdiction o' x r ho' hx
        subst e
        exact hnp hpy
      · exact hny hy
      · have e := w.exclusive_jurisdiction o' o r ho' ho
        subst e
        exact hnpo hpy
    | take_vs_defend x y r hxy _ =>
      rcases h₁.2 with ⟨hx, _⟩ | ⟨hny, _⟩
      · exact hxy (w.exclusive_jurisdiction x y r hx h₂.2)
      · exact hny h₂.2
    | take_vs_intervene x y z r f hxy _ =>
      have hj : w.HasJurisdiction y r := by
        rcases h₂.2.1 with ⟨_, _, hj, _⟩ | ⟨rfl, _⟩
        · exact hj
        · exact w.self_sovereignty y
      rcases h₁.2 with ⟨hx, _⟩ | ⟨hny, _⟩
      · exact hxy (w.exclusive_jurisdiction x y r hx hj)
      · exact hny hj
    | intervene_vs_resist z x y r f _ =>
      exact h₂.2 ⟨y, r, h₁.2.1, h₁.2.2.1, h₁.2.2.2⟩
    | strike_vs_resist _ _ _ _ =>
      exact hnag h₁.2.2
    | stop_vs_act _ _ _ =>
      exact h₁
  owner_use _ _ hj hl := Or.inl ⟨hj, hl⟩
  licensed_use o _ _ ho hxo hp := Or.inr ⟨o, ho, hxo, hp⟩
  owner_defend _ _ _ hxy hj := ⟨hxy, hj⟩
  body_resist _ _ _ hxz hnl := ⟨hxz, hnl⟩
  enforce_defense _ _ _ _ _ hzx hag hent hprop := ⟨hzx, hag, hent, hprop⟩
  enforce_recovery z y o r hzy hoy ho hnp hent := by
    rcases hent with rfl | hnd
    · exact ⟨hzy, Or.inl ⟨ho, hnp⟩⟩
    · exact ⟨hzy, Or.inr ⟨fun hy => hoy (w.exclusive_jurisdiction o y r ho hy),
        o, ho, hnp, hnd⟩⟩
  standing z v r hne :=
    ⟨fun _ _ ⟨_, _, hent, _⟩ => hne hent,
     fun hv _ ⟨_, h⟩ => by
      rcases h with ⟨hz, _⟩ | ⟨_, o, ho, _, hnd⟩
      · exact hne (Or.inl (w.exclusive_jurisdiction z v r hz hv))
      · have e := w.exclusive_jurisdiction o v r ho hv
        subst e
        exact hne (Or.inr hnd)⟩
  avoidable_perm _ _ := True.intro

/-! ## A concrete example -/

inductive Person where
  | victim | assailant | bystander
  deriving DecidableEq

inductive Thing where
  | body (p : Person)
  | bike
  deriving DecidableEq

/-- The assailant is trying to take control of the victim's body. No one has declined
    enforcement. Force is measured on a numeric scale, and for illustration only, any
    force of level 1 or less counts as proportionate. -/
def assaultWorld : World Person Thing Nat where
  body := Thing.body
  body_injective _ _ h := Thing.body.inj h
  HasJurisdiction p r := r = .body p ∨ (r = .bike ∧ p = .victim)
  Holds p r := r = .body p ∨ (r = .bike ∧ p = .victim)
  hist :=
    { FirstAt := fun t p r => t = 0 ∧ (r = .body p ∨ (r = .bike ∧ p = .victim))
      GaveAt := fun _ _ _ _ => False
      DeceivedAt := fun _ _ _ _ => False
      CoercedAt := fun _ _ _ _ => False
      TookAt := fun _ _ _ _ => False
      DestroyedAt := fun _ _ _ => False
      InjuredAt := fun _ _ _ => False
      AgreedAt := fun _ _ _ => False
      AgreementDeceivedAt := fun _ _ _ => False
      AgreementCoercedAt := fun _ _ _ => False
      Outstanding := fun _ _ _ => False
      CompensatesAt := fun _ _ _ _ => False
      Alienable := fun r => r = .bike
      Capable := fun _ _ => True }
  now := 0
  Attempting p q r := p = .assailant ∧ q = .victim ∧ r = .body .victim
  Declines _ _ := False
  Permits _ _ _ := False
  Guardian _ _ := False
  Provides _ _ := True
  Contest _ _ := False
  InScope _ _ _ := False
  Proportionate f _ _ _ := f ≤ 1
  title_rule _ _ := ⟨fun h => ⟨rfl, h⟩, fun h => h.2⟩
  body_inalienable _ h := by cases h
  holds_body _ := Or.inl rfl
  body_first _ := ⟨0, Nat.le_refl 0, rfl, Or.inl rfl⟩
  first_unique _ _ x y r hx hy := by
    refine ⟨?_, hx.1.trans hy.1.symm⟩
    rcases hx.2 with rfl | ⟨rfl, rfl⟩ <;> rcases hy.2 with h | ⟨h, rfl⟩
    · exact Thing.body.inj h
    · cases h
    · cases h
    · rfl
  gave_unique _ _ _ _ _ h _ := h.elim
  compensation_unique _ _ _ _ _ h _ := h.elim
  wrong_creates_debt _ _ _ hw := by
    rcases hw.2 with ⟨_, h, _⟩ | ⟨_, h, _⟩ | h <;> exact h.elim
  debt_requires_source _ _ _ h := h.elim
  paid_stays_paid _ _ _ _ _ _ _ _ h := h
  first_in_time _ _ _ _ _ h _ := h.elim
  permits_unique _ _ _ _ h _ := h.elim
  held_has_first p _ hy := ⟨0, Nat.le_refl 0, p, rfl, hy⟩
  proportionate_exists _ _ _ _ := ⟨1, Nat.le_refl 1⟩

/-- In `assaultWorld`, the bystander may use force 1 and the assailant may not resist it;
    the bystander may not use force 5 and the assailant may resist it. -/
theorem bystander_example :
    (JSystem assaultWorld).Perm
        (Act.Intervene .bystander .assailant .victim (.body .victim) 1) ∧
    (JSystem assaultWorld).ObligRefrain (Act.Resist .assailant .bystander 1) ∧
    (JSystem assaultWorld).ObligRefrain
        (Act.Intervene .bystander .assailant .victim (.body .victim) 5) ∧
    (JSystem assaultWorld).Perm (Act.Resist .assailant .bystander 5) := by
  have H := consistent assaultWorld
  have hag : assaultWorld.Aggressing .assailant .victim (.body .victim) :=
    Or.inl ⟨⟨rfl, rfl, rfl⟩, by decide, Or.inl rfl, Or.inl rfl⟩
  obtain ⟨h1, h2⟩ := defense_of_others H .bystander .assailant .victim (.body .victim) 1
    (by decide) hag (Or.inr fun ⟨h, _⟩ => h) (Nat.le_refl 1) id
  obtain ⟨h3, h4⟩ := excessive_force_forbidden H .bystander .assailant .victim
    (.body .victim) 5 (by decide) (fun _ _ _ _ (h : 5 ≤ 1) => absurd h (by decide)) id
  exact ⟨h1, h2, h3, h4⟩

/-! ## Mutual combat -/

inductive Boxer where
  | red | blue
  deriving DecidableEq

/-- Two boxers in a match they have both agreed to, with every move within its scope.
    Each owns only their own body. No one is aggressing. -/
def boxingWorld : World Boxer Boxer Nat where
  body := id
  body_injective _ _ h := h
  HasJurisdiction p r := r = p
  Holds p r := r = p
  hist :=
    { FirstAt := fun t p r => t = 0 ∧ r = p
      GaveAt := fun _ _ _ _ => False
      DeceivedAt := fun _ _ _ _ => False
      CoercedAt := fun _ _ _ _ => False
      TookAt := fun _ _ _ _ => False
      DestroyedAt := fun _ _ _ => False
      InjuredAt := fun _ _ _ => False
      AgreedAt := fun _ _ _ => False
      AgreementDeceivedAt := fun _ _ _ => False
      AgreementCoercedAt := fun _ _ _ => False
      Outstanding := fun _ _ _ => False
      CompensatesAt := fun _ _ _ _ => False
      Alienable := fun _ => False
      Capable := fun _ _ => True }
  now := 0
  Attempting _ _ _ := False
  Declines _ _ := False
  Permits _ _ _ := False
  Guardian _ _ := False
  Provides _ _ := True
  Contest _ _ := True
  InScope _ _ _ := True
  Proportionate _ _ _ _ := True
  title_rule _ _ := ⟨fun h => ⟨rfl, h⟩, fun h => h.2⟩
  body_inalienable _ h := h
  holds_body _ := rfl
  body_first _ := ⟨0, Nat.le_refl 0, rfl, rfl⟩
  first_unique _ _ _ _ _ hx hy := ⟨hx.2.symm.trans hy.2, hx.1.trans hy.1.symm⟩
  gave_unique _ _ _ _ _ h _ := h.elim
  compensation_unique _ _ _ _ _ h _ := h.elim
  wrong_creates_debt _ _ _ hw := by
    rcases hw.2 with ⟨_, h, _⟩ | ⟨_, h, _⟩ | h <;> exact h.elim
  debt_requires_source _ _ _ h := h.elim
  paid_stays_paid _ _ _ _ _ _ _ _ h := h
  first_in_time _ _ _ _ _ h _ := h.elim
  permits_unique _ _ _ _ h _ := h.elim
  held_has_first p _ hy := ⟨0, Nat.le_refl 0, p, rfl, hy⟩
  proportionate_exists _ _ _ _ := ⟨0, trivial⟩

/-- THEOREM 14 (Mutual combat is left open): in an agreed boxing match, the premises
    neither forbid nor require permitting the punches. With strikes in agreed contests
    permitted, every premise holds, and both the punch and the block are permitted at once,
    even though they physically conflict. With such strikes forbidden, every premise
    also holds. So narrowed compossibility no longer rules out consensual fighting, and no
    premise rules it in. -/
theorem mutual_combat_undetermined :
    JurisdictionUPB (JSystem boxingWorld True) boxingWorld ∧
    (JSystem boxingWorld True).Perm (Act.Strike .red .blue 1) ∧
    (JSystem boxingWorld True).Perm (Act.Resist .blue .red 1) ∧
    JurisdictionUPB (JSystem boxingWorld False) boxingWorld ∧
    ¬ (JSystem boxingWorld False).Perm (Act.Strike .red .blue 1) := by
  refine ⟨consistent _ True, ⟨trivial, by decide, trivial, trivial, trivial, trivial, trivial⟩,
    ⟨by decide, ?_⟩, consistent _ False, fun h => h.1⟩
  rintro ⟨_, _, (⟨h, _⟩ | ⟨_, _, h, _⟩), _⟩ <;> exact h

end UPB2

#print axioms UPB2.World.self_sovereignty
#print axioms UPB2.World.exclusive_jurisdiction
#print axioms UPB2.World.acquisition
#print axioms UPB2.World.title_depends_only_on_history
#print axioms UPB2.History.only_ways_to_gain_title
#print axioms UPB2.History.invalid_transfer_keeps_title
#print axioms UPB2.World.fraud_or_duress_victim_keeps_title
#print axioms UPB2.History.destruction_wrongs
#print axioms UPB2.World.restitution_owned
#print axioms UPB2.World.earlier_victims_first
#print axioms UPB2.World.no_restitution_from_body
#print axioms UPB2.World.no_debt_without_source
#print axioms UPB2.World.invalid_agreement
#print axioms UPB2.History.consent_requires_capacity
#print axioms UPB2.History.incapable_transfer_keeps_title
#print axioms UPB2.no_culpability_without_capacity
#print axioms UPB2.incapable_aggressor_may_be_stopped
#print axioms UPB2.incapable_keep_rights
#print axioms UPB2.World.anyone_may_help_incapable
#print axioms UPB2.World.provide_or_relinquish
#print axioms UPB2.rescue_from_neglect
#print axioms UPB2.rescue_available
#print axioms UPB2.History.taking_wrongs
#print axioms UPB2.borrower_must_return
#print axioms UPB2.consensual_bodily_contact
#print axioms UPB2.restitution_collection
#print axioms UPB2.History.others_cannot_transfer_your_title
#print axioms UPB2.History.no_wrong_to_oneself
#print axioms UPB2.no_stopping_self_harm
#print axioms UPB2.freedom_of_association
#print axioms UPB2.no_trespass
#print axioms UPB2.licensed_use_and_owner_yields
#print axioms UPB2.fraud_or_duress_recovery
#print axioms UPB2.premises_force_exclusivity
#print axioms UPB2.no_take_from_owner
#print axioms UPB2.bodily_non_aggression
#print axioms UPB2.peaceful_may_resist
#print axioms UPB2.property_non_aggression
#print axioms UPB2.no_take_from_sole_claimant
#print axioms UPB2.recovery
#print axioms UPB2.third_party_recovery
#print axioms UPB2.rescuer_must_return
#print axioms UPB2.vetoed_recovery
#print axioms UPB2.no_exemption
#print axioms UPB2.defense_of_others
#print axioms UPB2.defense_available
#print axioms UPB2.excessive_force_forbidden
#print axioms UPB2.vetoed_defense
#print axioms UPB2.no_stopping_permitted_acts
#print axioms UPB2.no_force_against_avoidable
#print axioms UPB2.no_victimless_crime_enforcement
#print axioms UPB2.no_assault
#print axioms UPB2.no_assault_on_peaceful
#print axioms UPB2.no_role_exemption
#print axioms UPB2.compossible_iff_decisive
#print axioms UPB2.consistent
#print axioms UPB2.bystander_example
#print axioms UPB2.mutual_combat_undetermined
