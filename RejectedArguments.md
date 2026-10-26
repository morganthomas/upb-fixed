# Rejected Arguments from *UPB*

Stefan Molyneux's *Universally Preferable Behaviour* (2007) presents itself as "a rational proof of secular ethics." This note goes through the arguments in the book that the formalization in `UPBJurisdiction.lean` does **not** rely on, and explains why each one fails.

Rejecting an argument is not the same as rejecting its conclusion. Several conclusions the book argues for badly, such as self-ownership, property rights and self-defense, are established in the formalization by other routes. Where that's the case, the entry says so. `Conclusions.md` lists what the formalization does establish, and `Premises.md` lists what it assumes.

Quotations are brief and cited by the book's section headings. They are used for the purpose of criticism.

## 1. The "proofs" that universally preferable behaviour exists

Part 1 of the book tries to show that "universally preferable behaviour" (UPB) is a valid concept, and then treats ethics as a branch of it. Every one of these arguments slides between two meanings of "preferable": what someone prefers or must do *to achieve a goal*, and what everyone is *morally bound* to do.

### 1.1 Arguing against UPB demonstrates UPB

> "Arguing against the validity of universally preferable behaviour demonstrates universally preferable behaviour." (*UPB: Five Proofs*)

**The argument.** Anyone who argues that UPB is invalid shows a preference for truth over falsehood, and so concedes that some behaviour is universally preferable.

**Why it fails.** At most, this shows that people who argue accept norms *of argument*: aim at truth, avoid contradiction. Those norms are conditional on taking part in a debate, and nobody thinks they can be enforced by force. Nothing follows about which acts are morally binding on everyone, still less about which may be enforced. The book itself later separates enforceable "ethics" from unenforceable "aesthetics," and the norms of debate fall on the aesthetic side by its own test. A proof that "some behaviour is preferable for arguers" can't carry the weight of "rape is evil."

### 1.2 Correcting someone implies a universal preference

> "Your preference for me to correct my error is not subjective, but objective, and universal." (*Arguments and Universality*, Premise 4)

**Why it fails.** It is the same move as 1.1. That truth is the goal *of inquiry* makes accuracy the standard for beliefs; it doesn't make anything binding on conduct generally. And "objective" is doing double duty. A preference can be *about* an objective matter (whether the earth is round) without itself being binding on anyone.

### 1.3 Anyone alive must have followed UPB

> "...if he is alive to argue, he must have followed universally preferred behaviours such as breathing, eating and drinking." (*UPB: Five Proofs*)

**Why it fails.** Breathing and eating are necessary *for staying alive*. That is a fact about biology, a hypothetical "must": if you want to live, you must eat. The book itself grants this earlier: "*If* he wants to live, then he *must* eat. However, his choice to live or not remains his own" (*The Discipline of Theoretical Ethics*). A hypothetical necessity binds only those who have the goal. It says nothing about what anyone may do to others.

### 1.4 Everyone believes in moral rules

> "All men believe in universally preferable behaviour." (*UPB: Five Proofs*)

**Why it fails.** That people believe in moral rules is evidence about people, not about whether the rules are valid. The book elsewhere insists that "Principles are not democratic" (*The Discipline of Theoretical Ethics*). It can't then use near-universal belief as proof. The premise is also doubtful as stated, since moral skeptics and nihilists exist.

### 1.5 People make similar choices

> "Therefore not all choices can be equal." (*UPB: Five Proofs*)

**Why it fails.** That most people prefer eating to starving shows that choices aren't random, not that any choice is morally required. This argument moves from what people *do* prefer to what they *should* prefer, which is exactly what the book warns against when it says universal preferences concern "what people *should* prefer, not what they always *do* prefer" (*Preferences and Universality*).

### 1.6 The evolutionary argument

> "Since man is the most successful species, and man's most distinctive organ is his mind..." (*UPB: Five Proofs*)

**Why it fails.** Evolution selects for whatever helps genes spread. That includes cooperation, but also deception, theft and violence where they pay. An evolutionary story can explain why moral intuitions exist; it can't show which of them are correct. The argument also rests on a contested claim ("most successful") and an unexplained step from "the mind helped us survive" to "UPB is valid."

### 1.7 "Preferable" means "objectively required"

> "'Universally preferable,' then, translates to 'objectively required'..." (*Preferences*)

**Why it fails.** This is where the conditional and the categorical are merged. Every example the book gives of "objectively required" behaviour is conditional: *if* you want to live, eat; *if* you want truth, use the scientific method. Ethics, as the book wants it, is categorical: don't rape, full stop. Renaming the conditional "universally preferable" and then using that name for the categorical doesn't bridge the gap. It is the gap Hume pointed out, which the book acknowledges in the same chapter.

### 1.8 Peaceful debate as the universally preferable method

> "...the only consistent argument for the *value* of violence is the *use* of violence." (*Arguments and Universality*, Premise 7)

**Why it fails.** That someone chooses to *debate* a question doesn't commit them to settling *every* dispute by debate. Someone can coherently argue, peacefully, that violence is sometimes justified, as defenders of self-defense or just war do. The claim that the only consistent defense of violence is to use it confuses the method of an argument with its subject.

**What survives.** The book's underlying idea, that a moral system exists to settle conflicts rather than leave everyone "pointing guns at each other's faces," is the motivation for compossibility (P1) in the formalization. P1 is stated there as a premise to be accepted or rejected, not as something debate forces on you.

## 2. Treating "may" as "must"

The book's tests of moral propositions repeatedly refute a claim nobody makes, that some aggression is *obligatory*, and treat that as refuting the claim people actually make, that it is *permitted*. This was the problem that started the formalization.

### 2.1 "Two men in a room"

> "...it is impossible for two men in a single room to *both be moral at the same time*..." (*The First Test: Rape*)

**The argument.** If rape (or murder, or theft) were good, then not doing it would be evil. Two men in a room couldn't both be good at once, since only one can be the aggressor. So the proposal is self-contradictory.

**Why it fails.** That refutes "everyone *must* rape at all times," which no one proposes. The predator's claim is that rape is *permitted*. Under a permission, both men can be moral at once: one rapes, the other is merely not required to. The same applies to the murder version, where Bob and Doug strangle each other (*The Second Test: Murder*), and to the theft version, "If everyone *should* steal, then no one *will* steal" (*UPB: The Practice*).

### 2.2 The coma test

> "If I say that giving to charity is a moral absolute, then clearly not giving to charity would be immoral." (*The Coma Test*)

**Why it fails.** It makes the same mistake. The coma test shows that an *obligation* to act can't apply to someone unable to act. It has no force against a *permission*, which a man in a coma doesn't violate by lying still. The test is sound against "you must do X at all times." It is useless against "you may do X."

### 2.3 Ruling out "may" by fiat

> "(Note that I cannot propose that 'personal preferences *may* be violently inflicted upon other people'..." (*3. Personally Positive*)

**Why it fails.** The book briefly notices the permissive version, then excludes it by stipulation: moral rules must be "absolute and universal," so a permission doesn't count. But a permission can be perfectly universal: "everyone may defend themselves" is one. Declaring permissions out of bounds doesn't refute them; it changes the subject.

**What survives.** Refuting permitted aggression needs an extra premise. The formalization uses compossibility (P1) together with owners' standing to defend (P3), which forbid aggression without any appeal to obligation.

## 3. Universality and symmetry

### 3.1 Moral rules like laws of physics

> "...it is like proposing a physics theory that says that some rocks fall down, while others fall up." (*UPB: The Practice*)

**Why it fails.** Physical laws apply uniformly because the same causes produce the same effects. Moral rules can be universal while still giving different verdicts in different situations. "Whoever owns a thing may use it" is universal, yet it permits me to use my car and forbids you to. The book's own examples show this. It is right that a sleeping man doesn't "become the *opposite* of a man" (*The Second Test: Murder*). But a man who is mid-attack is in a different moral situation from one who isn't, which is why defense against him is permitted. Universality forbids rules that turn on *who* someone is. It doesn't forbid rules that turn on what they are *doing*.

### 3.2 "Tarantino morality" and the FUBAR stalemate

> "This kind of 'Tarantino morality' always ends up with everyone in a state of mute paralysis, pointing guns at each other's faces..." (*6. Aesthetically Negative*)

> "Well *I* now represent the ideal concept 'ANTI-FUBAR'..." (*Government, Religion and UPB*)

**The argument.** If Bob may use force to impose his preferences, then by universality so may Doug. Their permissions cancel out in a stalemate, so the rule is invalid.

**Why it fails.** There are two problems.
- **Symmetric permissions aren't contradictory.** Two people each permitted to fight produces a fight, not a logical contradiction. Calling the result "paralysis" is an empirical prediction, and arguably a false one: the stronger party wins.
- **The predator doesn't need a symmetric rule.** "The stronger may take from the weaker" is universal, privileges no one by name, and doesn't cancel out. The formalization proves this. `archive/UPBSymmetry.lean` gives an agent-neutral rule of exactly this kind that satisfies the other premises (`neutrality_does_not_imply_P2`). The symmetry argument works only if "universal" is strengthened to "every permission to coerce is mutual," and that stronger premise assumes the conclusion.

**What survives.** The point that a claimed justification can't rest on a made-up authority survives as Theorem 8 (no exemptions for roles), together with the result that title can't be created by decree.

## 4. Property and self-ownership

### 4.1 Self-ownership from controlling your own speech

> "...it would be eminently fair for you to ask me who is working my vocal chords and mouth." (*The Third Test: Theft*)

**Why it fails.** That I *control* my body shows, at most, that I'm responsible for what I do with it. It doesn't show that I have a *right* to it that others must respect. Control is a fact; ownership is a norm. A slave controls his vocal chords too. The argument moves from "is" to "ought" at exactly the point the book earlier said that move can't be made.

**What survives.** The formalization keeps the *fact*, that each person controls and first possessed their own body, and derives self-ownership from a separate normative premise, title from first possession (P0).

### 4.2 Theft both affirms and denies property

> "...theft in practice is both an affirmation of property rights and a denial of property rights." (*Testing "Theft"*)

**The argument.** The thief denies the victim's property right but wants to keep the loot, which affirms his own. Since he holds both, theft is self-contradictory.

**Why it fails.** Wanting to keep something isn't claiming a *right* to it. The book itself treats the desire to control an object as "the very definition of property rights" (*Testing "Theft"*), which is the equivocation. A thief can consistently hold "I may take whatever I can hold," with no general theory of property at all. There's also nothing contradictory in denying everyone else's property rights while asserting no rights of your own.

### 4.3 Partial ownership leads to infinite regress

> "...a 'domino effect' of infinite regression, wherein everybody ends up with infinitely small ownership rights..." (*Property as Universality*)

**Why it fails.** The argument assumes that if you may own only half of each thing, then whoever receives the other half must also split it, and so on. But a rule of partial or shared ownership needn't apply to itself that way. Joint ownership, shares in a company and community property all exist without regress. Whatever their merits, they aren't incoherent.

**What survives.** Exclusive ownership is derived in the formalization (`World.exclusive_jurisdiction`, Theorem 0) from the physical fact that two people can't use one scarce thing at once, not from a regress.

## 5. Self-defense through the seven categories

> "Self-defense cannot be 'evil,' since evil by definition can be prevented through force." (*Self-Defense*)

**Why it fails.** The book first defines "evil" as what may be prevented by force, then concludes that whatever is evil may be prevented by force. That is circular: the permission to defend is built into the definition. The surrounding argument, sorting self-defense into the book's seven categories and ruling out six, depends on that definition and on treating each category as an obligation, the error of section 2.

**What survives.** The formalization makes the permission to defend an explicit premise (P3b, P3d, P5a), and derives what follows from it, such as that the aggressor may not resist proportionate force and that excessive force is forbidden.

## 6. Children as "an effect of the body"

> "...children are an effect of the body, then parents are responsible for their children." (*Child Raising*)

**Why it fails.** If being "an effect of your body" made you responsible for something, it would also seem to make you its *owner*, since the book derives ownership of products from the same idea ("we own that which we produce," *Property and UPB*). That would make children their parents' property, which the book rejects. The premise proves either too much or nothing.

**What survives.** The book's better analogy, a guardian who keeps someone dependent in custody while not providing for them, like the husband who locks his wife in the basement, is the basis for "provide or relinquish" in the formalization (Theorem 13).

## 7. The competence argument against the social contract

> "Either I am capable of making competent decisions, or I am not." (*Practicality*)

**The argument.** If I'm competent, subjecting myself to lifelong force is invalid; if I'm not, my decision to do so is invalid; either way the social contract fails.

**Why it fails.** Delegating decisions to others is often a competent choice, as in hiring a doctor or a financial adviser. The book's own analogy, choosing a doctor, shows that someone can competently pick an expert without being able to make the expert's decisions themselves. So competence doesn't rule out delegation. Whether a *lifelong, unrevocable* delegation enforced by force is valid is a real question, but this dilemma doesn't settle it.

**What survives.** The conclusion that no one can bind themselves to lifelong control follows in the formalization from P0b, which makes bodies non-transferable. The conclusion that no one can bind others, including their children, follows from the rule that only you can obligate yourself (`no_debt_without_source`).

## 8. Arguments that aren't arguments in ethics

### 8.1 Empirical "confirmations"

> "Since we have proven above that universal property rights is the only valid moral theory, this explains at the most fundamental level why communism is such a disaster..." (*The free-market economy*)

> "...UPB would help us easily predict that public schools would provide education of low quality." (*Public Education*)

**Why it fails.** These treat economic and historical outcomes as tests of a moral theory. A theory of what people *may* do doesn't predict how well institutions perform. And if it did, its failures would count against it as much as its successes count in its favor, yet the book counts only the successes. The book's table even proposes that "If communism succeeds relative to its stated goals, theories based on the universal validity of property rights are incorrect" (*UPB: The Practice*). That makes property rights hostage to economic performance, which no rights theory should accept.

### 8.2 God's nonexistence by definition

> "That which exists must be detectable; God cannot be detectable, but God exists – therefore that which does not exist, exists." (*Existence versus Non-Existence*)

**Why it fails.** The argument defines "existence" as detectability, then concludes that anything undetectable doesn't exist. That begs the question against anyone who thinks something might exist undetected. Whatever its merits, it is outside ethics, and nothing in the formalization depends on it.

### 8.3 "The government" as a null zone

> "What we call 'the government' is merely another example of this *null zone*..." (*UPB In Action*)

**Why it fails.** That "the government" is an abstraction made of individuals is true, but it doesn't settle anything. Corporations, clubs and families are abstractions in the same sense, and the book doesn't conclude that they have no standing. The real work is done by a different claim: that no individual gains permissions by acting in an official role.

**What survives.** That claim, that no role, office or majority creates an exemption, is Theorem 8 in the formalization, and title can't be created by decree or vote (`title_depends_only_on_history`).

## Summary

| Argument | Book section | Main flaw | Survives in the formalization as |
|---|---|---|---|
| Arguing against UPB demonstrates UPB | *UPB: Five Proofs* | Norms of debate aren't enforceable ethics | — |
| Correction implies universal preference | *Arguments and Universality* | Same as above | — |
| Alive, so followed UPB | *UPB: Five Proofs* | Hypothetical "must" isn't moral | — |
| Everyone believes in moral rules | *UPB: Five Proofs* | Belief isn't validity | — |
| Similar choices | *UPB: Five Proofs* | "Do" isn't "should" | — |
| Evolution | *UPB: Five Proofs* | Explains intuitions, doesn't justify them | — |
| "Preferable" = "required" | *Preferences* | Conditional renamed categorical | — |
| Peaceful debate | *Arguments and Universality* | Method confused with subject | Motivation for P1 |
| Two men in a room | *The First Test: Rape* and after | "May" treated as "must" | P1 with P3 |
| Coma test | *The Coma Test* | Refutes obligations only | — |
| "May" excluded by fiat | *3. Personally Positive* | Stipulation, not argument | — |
| Rocks falling up | *UPB: The Practice* | Universal rules can be relational | Agent neutrality |
| Tarantino / FUBAR stalemate | *6. Aesthetically Negative*, *Government, Religion and UPB* | Symmetric permissions aren't contradictory; asymmetric rules can be universal | Theorem 8; title not by decree |
| Self-ownership from speech | *The Third Test: Theft* | Control isn't a right | P0 plus first possession of the body |
| Theft affirms and denies property | *Testing "Theft"* | Wanting isn't claiming a right | — |
| 50% regress | *Property as Universality* | No regress follows | Exclusivity, derived |
| Self-defense via categories | *Self-Defense* | Circular definition of "evil" | P3b, P3d, P5a |
| Children as effects of the body | *Child Raising* | Proves too much | "Provide or relinquish" |
| Competence dilemma | *Practicality* | Delegation can be competent | P0b; only you can obligate yourself |
| Empirical confirmations | *Additional Proofs*, *UPB: The Practice* | Outcomes don't test rights | — |
| God by definition | *Existence versus Non-Existence* | Begs the question; not ethics | — |
| Government as null zone | *UPB In Action* | Abstraction proves nothing | Theorem 8 |

*Quotations from Stefan Molyneux, Universally Preferable Behaviour: A Rational Proof of Secular Ethics (2007), are reproduced briefly for the purpose of criticism and commentary.*
