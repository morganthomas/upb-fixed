# Known Limitations of the Jurisdiction-Route Formalization

This note covers `UPBJurisdiction.lean`, the version of the repaired UPB argument that drops the agent-symmetry premise (P2) and rests on title from first possession, compossibility, owner standing, and enforcement with a veto.

Lean has checked that every theorem in that file follows from its premises, and that the premises are consistent with each other. That is all it checks. It does not check that the premises are true, or that the model captures everything that matters morally. The limits below are places where the model is simpler than the moral questions it is meant to address. None of them is a bug in the proofs. Each one marks a conclusion the formalization does not reach, or reaches only because a simplification was built in.

## 1. Proportionality is required but not defined

**What the model says.** Defensive force must be proportionate. An aggressor may not resist proportionate force from someone entitled to stop them, but may resist excessive force. "Proportionate" is an undefined term. The only thing assumed about it is that every aggression can be met with some proportionate force.

**Why it matters.** The formalization settles the *structure* of proportionality but none of its *content*. It cannot say whether lethal force against a mugger is proportionate, or whether restraint is always proportionate. It says only that *if* a use of force is proportionate, it is permitted and may not be resisted, and *if* it is not, it is forbidden and may be resisted. Disagreements about specific cases are disagreements about the meaning of the term, which the model deliberately does not fix.

The model also places no structure on force itself. It does not assume that milder force than a proportionate force is also proportionate, or that forces can be compared at all.

**Necessity is deliberately not required.** Proportionate force is permitted even when less force would have worked. This is a substantive position, not an oversight: many theories of self-defense do require necessity, and someone who holds that view will reject P5a as stated.

**What extending it would take.** Content can be added in small steps, each as an explicit premise about the term. Examples: an ordering on forces with the premise that milder force than a proportionate force is also proportionate, or particular cases fixed by stipulation ("non-injurious restraint is always proportionate").

## 2. After an aggression ends: restitution only

**What the model says.** Someone is aggressing only while they are actively trying to take something from its owner. Once the attempt stops, they are no longer liable to defensive force. What remains is **restitution**: the history records completed wrongs (takings, destruction and damage, injuries), and the victim acquires title to the designated compensation from the wrongdoer's property, which they may collect.

**What it still leaves out:**

- **Punishment** for a completed aggression, beyond compensation, is out of scope for now. The book endorses restitution but not retribution, and premises about punishment are among the most contested in rights theory.
- **Pursuit** of a fleeing attacker is left open. Collecting restitution can justify proportionate force after the fact, but only to recover the compensation. There is no general right to stop or detain someone for a completed wrong.

**Choices made in modeling restitution, which could be revisited:**

- **Necessity: wrong but excusable.** Breaking a stranger's window to save your life counts as a wrong (and so is forbidden, by Theorem 3F) that creates a duty of restitution. This follows the book's own position in *Lifeboat Scenarios*: "This is not to say that breaking the window to save your life is not wrong. It is, but it is a wrong that almost all of us would choose to commit rather than die." Nothing in the model formally excuses it; the excuse lives in our moral judgment of the person, not in the rules. The alternative is that such acts are *permitted but compensable* (Joel Feinberg's hiker who breaks into a cabin in a blizzard): the act would be permitted, and restitution still owed. Adopting it would need a premise permitting use of others' property in emergencies.
- **Restitution from property only.** Because bodies can't be transferred (P0b), a wrongdoer with no transferable property pays nothing, and the model has no compelled labor to work off a debt. Allowing that would mean weakening P0b, which makes these two premises pull against each other.
- **First in time.** A wrongdoer's property can go to a victim only once every victim with an older claim has been paid off. Claims are ranked by the date of the earliest wrong to each victim. Alternatives include sharing pro rata, or giving priority to the most serious wrongs.
- **No unit of value.** Whether a debt is still owed is an undefined term, and so is which property compensates it. This avoids pricing injuries in money and avoids conflict with subjective value theory. The cost is that the model can't check that a victim receives the right amount, that payments add up correctly, or that a debt is ever paid. Debts don't lapse, but nothing guarantees they are collected.
- **Strict liability.** Every recorded taking from an owner, every destruction or damage of another's property, and every injury creates a duty of restitution, regardless of fault or intention. A fault-based alternative would need a model of intention and negligence.

**Other limits of the restitution model:**

- **Nothing guarantees that anything is designated.** The theorems say what follows *when* compensation is designated, not that it always will be.
- **Whether a past injury was justified is recorded, not derived.** The record of injuries leaves out those inflicted in permitted defense or enforcement. The model can't check this, because facts about aggression and proportionality are recorded only for the present.
- **Only takings from the owner count as wrongs.** A robber who takes stolen goods from a thief owes the absent owner nothing under this record, although the owner may still recover the goods themselves. This is related to limitation 4.

## 3. The veto is all-or-nothing per resource

**What the model says.** An owner either declines enforcement by others for a given resource or does not. If they decline, no one else may intervene or recover that resource on their behalf.

**Why it matters.** Real choices are finer-grained. A victim might welcome help from a friend or a hired protection agency but not from a stranger, or accept help recovering property but not help that risks violence. The model can't express any of this.

**What fixing it would take.** Make the veto depend on the helper as well as the resource, so it records whom the owner declines. This is a small change: the premises and proofs would carry over almost unchanged.

## 4. Some takings do not count as aggression

**What the model says.** "Aggression" is defined narrowly: trying to take something from its owner *while the owner holds it*.

**Why it matters.** Suppose a thief has stolen a bike and a second robber takes it from the thief. Under this definition the robber is not aggressing against anyone. The owner is not holding the bike, and the thief is not its owner. The consequences:

- The premises give no one permission to use force to stop the robbery in progress on the owner's behalf. The model's rules for stopping aggression do not apply.
- Afterward, the owner may still recover the bike from the robber, and third parties may still recover it on the owner's behalf. These rules depend on ownership, not on the taking having been aggression.

So the owner's claim survives, but the model gives no one standing to forcibly prevent a taking of stolen property while it is happening.

**What fixing it would take.** Widen the definition of aggression to any taking by someone without title from anyone, on the owner's behalf. This needs care. The wider definition must not classify the owner's own recovery, or a legitimate rescue, as aggression.

## 5. Permissions are assumed, not derived

**What the model says.** Every permission to use force is a premise: defending what you own, recovering stolen property, intervening to stop aggression, and recovering on someone else's behalf.

**Why it matters.** The one structural principle in the model, compossibility (P1), can only rule permissions out. It can never grant one. So the formalization cannot show that defense or enforcement is permitted from anything more basic. What it *does* derive are the prohibitions that follow once those permissions are granted:

- the aggressor may not resist proportionate force;
- excessive force is forbidden;
- force may not be used to stop avoidable acts;
- the thief may neither keep using the property nor resist its recovery;
- a rescuer must give recovered property back.

It also shows that all the permissions fit together without contradiction. Someone who rejects a permission premise, for example by denying that bystanders may intervene at all, is not refuted by the formalization. They are disagreeing with a premise.

## Other simplifications worth knowing about

- **First possession is a bare fact.** The model records who possessed each thing first, but not how possession works: what counts as possessing land, how much of it, for how long, or whether mixing labor matters. Theories of original acquisition disagree about exactly these questions, and the model takes no side.
- **"Voluntary" is only partly defined.** A transfer counts as voluntary unless it was induced by deception or made under threat of initiated force. But "deception" and "threat" are themselves bare facts in the model. It doesn't say how much pressure counts as a threat, whether staying silent can deceive, or whether tacit consent counts as a transfer (living in a country, voting, accepting services). It also doesn't say what makes a contract binding. These questions decide the social-contract debate, and the model takes no side on them.
- **Contracts follow the title-transfer theory.** This is a contested choice; the alternative treats promises as creating obligations to perform. Consequences worth knowing:
  - **Promises to perform aren't enforceable as such.** If you promise to work and don't, the other party gets only what the contract made forfeit, never your labor. This follows from P0b.
  - **Breach isn't a further wrong.** There are no damages for breach beyond what the contract stipulates.
  - **No duty to rescue, even after starting one.** The book holds that if you dive in to save a drowning person, or announce that you will, you become responsible, because others rely on you. The title-transfer theory can't express a duty that arises from reliance rather than agreement, so the model doesn't capture this.
- **Contract terms are bare facts.** The model records that someone agreed to owe someone else, but not the terms: how much, when payments fall due, or which conditions apply. These are folded into the undefined "still owed" and "compensates." Whether given conduct counts as agreement is also a bare fact. That includes ordering a meal, and also living in a country, which is the tacit-consent question.
- **One queue for all creditors.** Victims of wrongs and contract creditors are paid in a single first-in-time queue. The alternative, putting victims of wrongs first on the ground that they didn't choose to take on the risk, is defensible too.
- **Capacity is all-or-nothing at each moment.** Someone either has the capacity to choose at a given time or doesn't. The book allows reduced responsibility, and admits that legal thresholds, such as age 18 or a given IQ, are practical approximations of a gradual transition. The model can't express partial capacity or degrees of blame.
- **Harms done without capacity still create a debt.** This applies strict liability consistently: a sleepwalker who breaks a window owes for it, though they aren't to blame. The alternative is that **no debt arises without capacity**. That is closer to the book's tone ("we would not call a man who stole while sleepwalking 'evil'"), but it leaves the victim to bear the loss. Adopting it would mean adding capacity to the definition of a wrong.
- **Guardians may only receive benefits for a child.** A child can receive gifts, but a guardian can't give away or sell the child's property, or agree to anything in the child's name, even in the child's interest. So a guardian can't sell clothes the child has outgrown. The alternative is to let guardians manage and transfer a child's property "in the child's interest." That would need another undefined term, and it would weaken the result that only you can obligate yourself.
- **No veto of help without capacity, including advance refusals.** Someone lacking capacity can't decline help, and no guardian can decline it for them. That includes an adult who is temporarily unconscious. An adult who, while capable, refuses certain help *in advance* (a "do not resuscitate" instruction, say) can't yet have that refusal respected once they lose capacity. Advance refusals are planned for later.
- **The parental duty is "provide or relinquish."** A neglectful guardian can be made to give up the child, never made to work. This follows the book's conclusion and its basement analogy. Rothbard, reasoning from the title-transfer theory alone, concluded instead that parents may let their children starve. The model avoids that conclusion by treating neglect in custody as aggression, not by recognizing a positive duty to feed.
- **Guardianship and adequate care are undefined.** The model doesn't say how guardianship arises (birth, adoption, taking in a foundling), or what counts as adequate care. Nor does it say who becomes the child's guardian after a rescue; guardianship is simply recorded, as a fact about each situation.
- **Animals are out of scope.** The model's agents are persons. The book's view, that animals aren't moral agents, is consistent with this but isn't formalized, and the model says nothing about whether animals have rights.
- **Agency isn't modeled.** No one can authorize someone else to make agreements or transfers for them. Title also can't be abandoned: once someone owns a thing, someone always does.
- **Consent to bodily contact uses the same machinery as lending.** A patient who consents to surgery is modeled as lending the surgeon the use of their body. Because a scarce thing can be lent to only one person at a time and the owner yields while it's lent, the patient technically yields the use of their own body during the operation. That fits a patient under anesthesia. It doesn't fit mutual contact, such as a boxing match or a dance, where both people use their bodies at once. The model would need shared use to express that.
- **Permissions are a snapshot.** The model records who currently has permission to use what, but not the terms. It has no duration, no conditions, and no rules for when an owner may revoke permission. While a permission lasts, the owner yields completely. Things that many people can use at once, such as a road or a park, aren't modeled, since a scarce thing can be lent to only one person at a time.
- **Bodies can't be transferred.** P0b rules out voluntary slavery. Some libertarians, such as Walter Block, defend voluntary slavery contracts; others, such as Murray Rothbard, reject them. Dropping P0b is easy, but then self-ownership holds only for people who haven't given their body away.
- **Using your own property never affects others.** In the model, using your own body or property can't damage anyone else's. That is why Theorem 7B (no forcible stopping of victimless crimes) can be stated without exceptions. Real uses can spill over: smoke, noise, pollution, a stray firework. The model can't yet say when such a use becomes an aggression, so 7B covers only uses with no such effects.
- **"Avoidable" is a bare label.** P4 says avoidable acts are permitted, and Theorem 7 derives that no one may forcibly stop them. But the model doesn't define which acts are avoidable. The book treats avoidability as a matter of degree; for example, a threat you can escape only by moving continents is barely avoidable. The model can't express degrees, and P4 is still stated rather than derived.
- **The veto still has to be assumed.** The standing premise (P5c) merges the two former vetoes into one principle. It is still a premise, though: nothing more basic in the model implies that an owner's refusal binds others.
