# Universally Preferable Behaviour (UPB): Formal Logic Audit & Map of Required Presuppositions

**Source Text Verified:** Stefan Molyneux, *Universally Preferable Behaviour: A Rational Proof of Secular Ethics* (Freedomain Library, Vol. 2, Version 1.0, October 2007, 134 PDF pages).

---

## 1. Structural & Deductive Map of Molyneux's 2007 *UPB*

- **Foreword & Introduction (pp. 7–19):** Rejects religious/mystical ethics and secular statism ("middle truths") and proposes that universal moral truths ("great truths", e.g., "stealing is wrong") must be derived directly from concrete interpersonal truths ("little truths", e.g., "stealing from me is wrong") via logic and the scientific method.
- **Part 1: Theory (pp. 20–61):**
  - *A Framework for Ethics (pp. 22–28):* Distinguishes personal preferences ("I like jazz") from objective truth claims ("The earth is round") and moral claims.
  - *Validating Frameworks & Consistency (pp. 29–43):* Argues that anyone debating ethics presupposes truth, logic, empirical reality, and the existence of Universally Preferable Behaviour (the performative contradiction / self-detonating statement argument, pp. 37–43).
  - *Positive vs. Negative Rules, Avoidability, and Categories of Action (pp. 44–61):* Argues that positive obligations ("thou shalt") cannot be practiced universally across all times and places, whereas negative prohibitions ("thou shalt not") can; introduces avoidability and the moral categories (Neutral, Personally Preferable, Aesthetically Preferable [APA/ANA], Good, Evil).
- **Part 2: Application (pp. 62–95):**
  - *Two Men in a Room ("Bob and Doug", pp. 64–74):* Tests asymmetric moral propositions ("Compossibility / Symmetry Test") on **First Test: Rape** (pp. 68–70), **Second Test: Murder & Assault** (pp. 71–74), and **Third Test: Theft & Property** (pp. 75–85).
  - *Ground Rules, Self-Defense, Child Raising, and Animal Rights (pp. 86–95):* Addresses exceptions based on biological capacity, implicit contracts in child raising, and why UPB applies only to rational humans.
- **Part 3: Practice & Conclusions (pp. 96–130):**
  - Applies UPB to refute bigotry/faith ("the Null Zone"), government, taxation, majority rule, and public education; summarizes the 12-step core proof in *Appendix A: UPB in a Nutshell* (p. 125) and *Appendix B: Moral Categories* (p. 126).

---

## 2. Step-by-Step Formal Logic Audit: The 6 Core Deductive Gaps

From a college-level formal logic perspective (first-order predicate logic, modal/deontic logic, and philosophy of action), a proof cannot derive normative conclusions ($\mathcal{O}\neg\phi$, "it is obligatory not to do $\phi$") from purely descriptive premises without normative axioms, nor can it rule out asymmetric universal rules without symmetry/agency axioms. Here are the exact six joints where UPB relies on unstated presuppositions:

### Gap 1: The Semantic Equivocation on "Preferable" & Hume's Is–Ought Bridge (pp. 22–28, 37–43, 125)
- **What Stef argues:** Living, thinking, and debating require biological/psychological preferences ("I prefer truth to falsehood," "I prefer life to death," p. 125 steps 6–8). From the fact that humans *do* prefer certain states, he concludes that certain behaviors are *Universally Preferable* in a normative, binding sense.
- **The Formal Flaw:** As J.S. Mill famously did in *Utilitarianism*, the text equivocates between two senses of **"preferable"**:
  1. **Descriptive/Psychological ($\text{Pref}(a, \phi)$):** Capable of being preferred, or actually preferred by agent $a$.
  2. **Normative/Deontic ($\mathcal{O}(\phi)$ or $\text{WorthyOfPreference}(\phi)$):** Binding upon agents such that they *ought* to respect or prefer $\phi$ regardless of their subjective desires.
  In standard deontic logic, no valid inference rule permits $\forall x\,\text{Pref}(x, \phi) \vdash \forall x\,\mathcal{O}(\phi)$ without an explicit bridge axiom.

### Gap 2: Performative Consistency in Discourse vs. Non-Discursive Action (pp. 37–43, 55–61, 125)
- **What Stef argues:** "Anyone who argues against UPB must be advocating that it is universally preferable that we should not believe in UPB—which is a self-contradiction" (pp. 40–42; p. 125 steps 7–8). Similarly, using force during a debate contradicts the peaceful nature of debate (pp. 58–60).
- **The Formal Flaw:**
  1. **Negation vs. Opposite Claim:** Denying a universal claim $\neg\forall x\,P(x)$ (moral skepticism: "there is no action that is universally obligatory") is logically equivalent to $\exists x\,\neg P(x)$, *not* $\forall x\,\neg P(x)$ ("it is universally obligatory not to believe in UPB"). Confusing $\neg\mathcal{O}(\phi)$ (permission/amoralism) with $\mathcal{O}(\neg\phi)$ (prohibition) is a classic modal scope fallacy.
  2. **The Silent Aggressor Problem:** Even if participating in a debate commits an agent to peaceful truth-seeking *while debating*, that pragmatic presupposition is conditional on choosing to debate ($\text{Debates}(a) \to \text{RespectsNorms}(a)$). It does not logically bind an agent who simply uses force without debating, or who values peaceful persuasion only instrumentally when convenient.

### Gap 3: Universal Quantification vs. Bilateral Agent Symmetry (pp. 31–43, 64–70)
- **What Stef argues:** Because physical laws (like gravity) apply identically to all atoms independent of time and place, valid moral laws must apply symmetrically and identically to all human beings ("Bob and Doug in a little room," pp. 64–67).
- **The Formal Flaw:** In first-order logic, a rule is **universally quantified** ($\forall x \forall y$) so long as it contains no proper names or indexicals—even if the predicate is relational and asymmetric. For example:
  $$\forall x \forall y\,\big(\text{Stronger}(x,y) \to \mathcal{P}(\text{Dominate}(x,y))\big)$$
  ("For all agents $x$ and $y$, if $x$ is stronger than $y$, $x$ may dominate $y$") is 100% universal, timeless, and consistent with physics (where larger masses exert greater gravitational acceleration on smaller masses). To rule out "might makes right," caste rules, or predatory egoism, one must explicitly presuppose **Normative Agent Symmetry (Moral Equality of Persons)**—that moral rules must be invariant under permutation of rational agents ($x \leftrightarrow y$) regardless of differences in physical power.

### Gap 4: The "Two Men in a Room" Compossibility Test & Simultaneous Execution (pp. 68–74)
- **What Stef argues:** To test whether "Rape is Good" or "Murder is Good" or "Rape is a Personal Preference" can be valid UPB, Stef puts Bob and Doug in a room and requires that *both* simultaneously act on the rule toward each other: if both want to rape each other, it becomes consensual sex (not rape); if both murder each other simultaneously, neither survives to enjoy the preference (pp. 68–74).
- **The Formal Flaw:**
  1. **Permissibility ($\mathcal{P}$) vs. Obligation ($\mathcal{O}$):** A defender of predation does not claim $\mathcal{O}(\text{Rape})$ ("everyone must rape everyone at all times"); they claim $\mathcal{P}(\text{Rape})$ ("forcing another is permissible when one desires and has the power"). Testing $\mathcal{P}(\phi)$ as if it were $\mathcal{O}(\phi)$ executed simultaneously by both parties is a category mistake—by that test, "buying a house from your neighbor" or "performing surgery on another person" would also fail if both had to perform the identical role on each other simultaneously.
  2. **What Stef is *actually* testing:** What makes rape, assault, and murder fail is not simultaneous physical execution, but **Normative Compossibility of Non-Interference Boundaries**: if every agent has an equal claim to govern their own body/choices, a rule permitting unilateral coercion grants Agent $A$ a right to override Agent $B$'s will while simultaneously granting Agent $B$ the right to resist/override Agent $A$'s will ($Right(A, \phi) \land Right(B, \neg\phi)$), generating a deontic contradiction in a system designed to resolve interpersonal conflict.

### Gap 5: From Bodily Non-Aggression to External Property Rights (pp. 75–85)
- **What Stef argues:** Theft violates UPB because "theft requires property" (just as rape requires lack of consent), and if theft were universalized, property ownership itself would be abolished, creating a self-contradiction (pp. 75–83).
- **The Formal Flaw:** Defining "theft" as "taking *legitimately owned* property without consent" makes "theft is wrong" an analytic tautology ("unjust taking is unjust"), which leaves completely unanswered *which* theory of property acquisition is valid (Lockean homesteading vs. Georgist commons vs. egalitarian shares vs. occupancy-and-use). To prove that taking an external object Bob built or homesteaded is immoral without begging the question, the system requires an explicit **Original Appropriation & Title Transfer Presupposition** connecting self-ownership and uncoerced labor/first-use to exclusive moral jurisdiction over external scarce goods.

### Gap 6: Positive Obligations to Children vs. the "Negative Rules Only" Principle (pp. 44–45, 88–95)
- **What Stef argues:** On pp. 44–45, UPB states that moral rules can *only* be negative prohibitions ("thou shalt not") because positive obligations cannot be practiced perpetually. Yet on pp. 88–95, parents have a binding positive obligation to feed and care for their children (and cannot starve them).
- **The Formal Flaw:** Without an explicit **Causal-Dependency / Fiduciary Creation Principle**, a strict "negative prohibitions only" axiom would allow a parent to claim that ceasing to feed an infant is mere non-action ("withholding my food/labor"). To make parental obligation deductively valid while preserving Peaceful Parenting, the system needs an explicit axiom that *voluntarily placing or bringing a vulnerable agent into a state of biological dependency creates an enforceable fiduciary duty of care until independence or voluntary transfer of guardianship*.

---

## 3. Map of Candidate Presuppositions (The Axiomatic Menu)

Because your goal is to turn UPB into a **strictly valid conditional/axiomatic proof of secular ethics** grounded in presuppositions that **reasonable people who want to share a peaceful, functional society will readily accept**, we can formulate the exact presuppositions required to close all six gaps.

Below is the map comparing **Three Tiers** of candidate presuppositions—from the weakest/most widely acceptable "Shared Peaceful Society" axioms (Tier A, recommended as our primary foundation) to Kantian/Discourse axioms (Tier B) and thicker Lockean/Hoppean axioms (Tier C).

| Logical Gap in UPB | Tier A: Minimal "Shared Peaceful Society" Presuppositions *(Recommended Core)* | Tier B: Rational Agency & Discourse Presuppositions | Tier C: Thick Lockean / Libertarian Presuppositions |
| :--- | :--- | :--- | :--- |
| **1. Meta-Ethical Purpose & Is–Ought Bridge** *(Why ethics binds)* | **P1 (The Social-Peace Conditional):** Ethics is the set of interpersonal rules required for rational agents to coexist in a peaceful, cooperative society rather than a state of violent conflict ("might makes right"). If an agent chooses peaceful social coexistence over war, they are rationally bound by the necessary conditions of that coexistence. | **P1-B:** Valuing truth and rational justification commits an agent to valuing the preconditions of rational agency in all discourse partners. | **P1-C:** Natural law teleology: human nature and biological survival objectively mandate a specific moral code. |
| **2. Scope of Bindingness** *(Closing the "Silent Aggressor" Escape)* | **P2 (Reciprocity of Social Standing):** Protection under the moral rules of a peaceful society is conditional on reciprocating those rules. Anyone who rejects peaceful resolution in favor of unilateral force forfeits moral immunity against defensive force. | **P2-B:** Argumentation Ethics: any propositional claim to justify action presupposes norms of non-aggression even outside active debate. | **P2-C:** Categorical moral realism: moral duties bind unconditionally regardless of an agent's desires or participation in society. |
| **3. Normative Agent Symmetry** *(Ruling out "Might Makes Right")* | **P3 (Formal Moral Equality / Symmetry):** Fundamental moral rules governing interpersonal conduct must be *agent-symmetric*—invariant under any permutation of rational agents ($A \leftrightarrow B$)—meaning no agent or group possesses an innate moral privilege to coerce others based on superior strength, status, or numbers. | **P3-B:** Kantian Universal Law: act only on maxims that all rational agents could simultaneously will as universal law without contradiction. | **P3-C:** Strict biological egalitarianism of natural rights across all members of *Homo sapiens*. |
| **4. Compossibility & Non-Interference** *(Fixing the "Two Men in a Room" Test)* | **P4 (Compossibility of Jurisdictions / Avoidability):** A valid system of interpersonal rules must assign compossible (mutually non-contradictory) spheres of decision-making authority so that all agents can simultaneously comply without conflict. Only negative prohibitions against unconsented boundary crossings (and never compulsory positive service to strangers) are universally compossible and avoidable. | **P4-B:** Kantian/Steiner Compossibility of Rights: a set of rights is valid iff no two agents' exercise of their rights can physically collide in the same spacetime/object. | **P4-C:** Explicit Axiom of Non-Aggression (NAP) assumed directly as a starting premise. |
| **5. Bodily & External Property Boundaries** *(Deriving Rape, Assault, Murder, and Theft Prohibitions)* | **P5 (Presumptive Self-Sovereignty & Conflict-Free Resource Rules):** (a) Each rational agent has exclusive moral jurisdiction over their own physical body (Why not someone else? By P3 Symmetry, any asymmetric claim fails). (b) Because humans must use external scarce resources to live and act, peaceful coexistence requires an objective, agent-symmetric, conflict-free rule for resource control: prior uncoerced appropriation/production (homesteading) and voluntary transfer (contract) establish presumptive title against latecomers. | **P5-B:** Embodied Agency Axiom: because agency is exercised through the body and ongoing projects, interfering with an agent's body or appropriated tools violates their status as a rational agent. | **P5-C:** Strict Lockean Labor-Mixing Axiom: mixing labor with unowned nature literally transfers metaphysical self-ownership into the object. |
| **6. Causal Responsibility & Peaceful Parenting** *(Positive Duties to Dependents)* | **P6 (Causal-Dependency & Fiduciary Duty):** While no agent owes unchosen positive service to independent strangers (P4), voluntarily causing a foreseeable harm, entering a contract, or bringing a biologically dependent human being (a child) into existence creates an enforceable positive duty of care and non-violent stewardship until independence or voluntary transfer of guardianship. | **P6-B:** Developmental Agency Principle: proto-agents (children) must be nurtured without violence so they can develop into full rational agents. | **P6-C:** Homesteading/trusteeship theory of parental guardianship. |

---

## 4. How the Minimal Presuppositions (P1–P6) Make UPB Deductively Valid

Once **P1–P6** are stated upfront as transparent axioms for anyone who wants a peaceful, rational society, Stef's core UPB engine works as a **strictly valid deductive proof**:

1. **Derivation of Bodily Non-Aggression (Against Rape, Assault, and Murder):**
   - By **P1** and **P4**, moral rules must assign compossible decision-making authority over scarce resources so agents can coexist without conflict.
   - A human body is a scarce, rivalrous resource. There are only three possible universal rules for control over Agent $A$'s body:
     1. *Asymmetric Rule (Slavery/Predation):* Some agents ($B$) own $A$'s body without owning their own, or the stronger owns the weaker. **Refuted by P3 (Agent Symmetry).**
     2. *Universal Communal/Shared Rule:* Every agent has an equal right to use every other agent's body at will. **Refuted by P4 (Compossibility) & Stef's "Two Men in a Room" Test:** if $A$ wills to use $B$'s body (rape/assault) and $B$ wills not to be used, their equal rights collide in a direct contradiction; no action can be taken without permission or violent conflict.
     3. *Universal Self-Sovereignty (P5a):* Every rational agent $x$ has exclusive jurisdiction over $x$'s own body. **Compossible, symmetric, and universally avoidable.**
   - **Conclusion 1:** Any unconsented physical interference with another rational agent's body (rape, assault, murder) is deductively invalid ($\mathcal{O}\neg\text{Aggress}$), and defensive force to stop an ongoing boundary violation is permissible (**P2**).

2. **Derivation of External Property & Prohibition of Theft/Fraud:**
   - Humans cannot survive or act without using external scarce objects (food, shelter, land, tools).
   - If no agent may establish exclusive control over an external object, or if any latecomer $B$ may seize what $A$ has produced or put to use, then:
     - Under **P3 (Symmetry)**, if $B$ has a right to take from the prior user $A$, then $A$ (once $B$ takes it) becomes the latecomer and has an equal right to immediately take it back from $B$, generating perpetual, unresolvable conflict (**violating P1 & P4**).
     - Only the symmetric distinction between **prior peaceful user/producer (homesteader/transferee)** and **latecomer** (**P5b**) allows peaceful, conflict-free use of external goods from the moment of acquisition forward.
   - **Conclusion 2:** Unconsented taking of legitimately acquired property (theft, robbery, fraud, and coercive taxation) is deductively invalid.

3. **Derivation of Voluntary Association, Peaceful Parenting, and Statelessness:**
   - **Aesthetics & Free Association:** Actions that do not cross bodily or property boundaries and can be avoided by choosing not to associate (rudeness, personal tastes, peaceful speech) cannot be violently prohibited (**P4**).
   - **Children & Peaceful Parenting:** Bringing a child into existence places them in biological dependency (**P6**), creating a positive duty to feed and shelter them, while **P3/P5a** prohibits initiating retaliatory or punitive violence (spanking/assault) against them.
   - **Rejection of the State:** Because "government" is defined by an asymmetric claim to tax (take property without individual consent) and monopolize law/force over non-consenting peaceful individuals, any moral justification of the State directly violates **P3 (Agent Symmetry)**, **P4 (Avoidability)**, and **P5 (Property)**.

---

## 5. Proposed Blueprint for the Supplemental Book

**Working Title Ideas:**
- *Completing UPB: The Axiomatic Proof of Secular Ethics*
- *Universally Preferable Behavior Contextualized: A Formal Deductive Reconstruction of Secular Ethics*

**Proposed Chapter Structure:**
1. **Chapter 1: Why Presuppositions Are a Feature, Not a Bug**
   - Why every deductive system in logic, mathematics (Euclid, Peano, ZFC), and physics requires explicit axioms.
   - Why accepting explicit presuppositions does not make ethics "arbitrary" or "merely subjective"—it makes ethics a transparent, objective *conditional proof* for everyone who wants to share a peaceful society.
2. **Chapter 2: Anatomy of Molyneux's *UPB* — What Works and Where the Logic Jumps**
   - A charitable, rigorous audit of the 2007 *UPB* text: separating Stef's brilliant insights (avoidability, asymmetric "middle truths", the two-person room test) from the six formal gaps (equivocation on "preferable", modal scope errors, symmetry vs. universality).
3. **Chapter 3: The Six Foundational Presuppositions of a Peaceful Society (P1–P6)**
   - Laying out the minimal axioms (Social Peace, Reciprocity, Agent Symmetry, Compossibility/Avoidability, Self-Sovereignty & Prior Appropriation, and Causal-Dependency Fiduciary Duty) and showing why no reasonable person you'd want as a neighbor could reject them.
4. **Chapter 4: Formalizing the UPB Engine (The Deductive Proof of Non-Aggression)**
   - Re-running the "Bob and Doug in a Room" tests (Rape, Assault, Murder, Self-Defense) with P1–P5a in place so the proofs are 100% airtight in first-order deontic logic.
5. **Chapter 5: Closing the Property Gap (From Self-Ownership to Theft & Fraud)**
   - How P3, P4, and P5b turn Stef's "Third Test: Theft" from a circular definition into a rigorous deduction of homesteading, contract, and the immorality of theft and fraud.
6. **Chapter 6: Positive Duties Without Contradiction (Contracts, Children, and Peaceful Parenting)**
   - Resolving the tension between UPB's "negative rules only" theorem and positive parental duties using P6 (Causal Dependency).
7. **Chapter 7: Refuting the "Middle Truths" (Statism, Taxation, and Majority Rule)**
   - Applying the completed axiomatic proof to government, democracy, and public institutions.
8. **Appendix: The Complete Symbolic Proof (Axioms, Definitions, and Theorems in Formal Notation)**
   - A clean, college-level formal logic reference sheet of the entire deductive system from P1–P6 to all core theorems.
