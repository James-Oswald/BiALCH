# Review 1

Formal issues in central proofs and definitions
Official Reviewby Program Committee jVSE31 Aug 2026, 12:59 (modified: 24 Sept 2026, 17:53)Program Chairs, Area Chairs, Senior Program Committee, Program Committee jVSE, Authors, Program Committee SubmittedRevisions
Paper Summary:
The paper introduces a new description logic with a non-classical semantics based on weak Kleene logic, which essentially extends the classical semantics by having up to 9 truth values, shows a reduction to classical description logic and based on this translation establishes tight complexity bounds of entailment checking. The logic is motivated by applications in neuro-symbolic reasoning, which otherwise does not play a major role in the paper.

The basic logic is 
, which extends 
 with role conjunctions in role assertions (
) and disallows negation, while preserving all other operators of 
 (GCIs, conjunction, disjunction, universal and existential role restrictions, top and bottom). Weak Kleene (wK) logic adds to the usual truth values t and f a third value e (truth unknown) which dominates for all connectives. AC goes one step further and considers as truth values pairs of values from this set 
, the intuitive meaning being that the first component is based on the evidence for the statement, while the second component of the pair is based on the evidence against the statement. For example, a truth value of 
 for a formula 
 would read as: there is evidence both for and against 
. A third logic, 
, is obtained from AC by restricting the nine possible truth values of AC to five truth values by ruling out those that are harder to justify, such as 
.

The semantics of 
 is extended to those three semantics wK, AC and 
 (the original logics already have a semantics for dealing with existential and universal restrictions). To show tight PSpace / ExpTime complexity bounds for reasoning with respectively acyclic and general TBoxes, the paper presents a translation first of 
 to 
 through the introduction of fresh concept names. The translation produces two classical TBoxes from a 
 one, where intuitively one handles the the classical truth values and the other one "meaningfulness" (can a truth value be established). A similar idea is used for AC (now using a TBox for positive and a TBox for negative evidence), and 
 is handled by adding additional axioms to restrict the possible truth values in an interpretation. Tight complexity results then directly follow, since all translations are linear and reasoning in the base logic is already PSpace / ExpTime complete.

Strengths:
tight complexity bounds for new logics
the paper is mostly well written and easy to follow
motivation in the timely topic of neuro-symbolic AI: indeed it is likely that non-classical semantics are needed to appropriately combine LLM outputs with logical reasoning.
Weaknesses:
the results themselves are not overly surprising
some design decisions for the logic are not well explained (see below)
the presentation has formal flaws
there are errors in central proofs and definitions
Justification of Recommendation:
I think the motivation from neuro-symbolic AI is justified, and it is nice to see that people are still looking at new description logics. That the logics remain in ExpTime (or PSpace in case of acyclic TBoxes) is not surprising, since 
 already has this complexity and semantics with a fixed number of truth values can usually be easily encoded without an increase in complexity (see for instance research on fuzzy description logics with finite truth values). Finding a good translation can however be tricky (an alternative approach could have been to introduce fresh names for the new truth values).

What is puzzling me (and worrying me a little bit) is the choice of the base logic 
: under classical semantics, there is no big difference to 
, since role conjunction only on the level of role assertions can easily be simulated by a pair of role assertions, and also concept negation can easily be simulated with the other operators at hand (e.g. 
 can be captured by a concept name 
 with two axioms 
 and 
). The latter point is also used in the hardness argument towards the end of the paper - then why not directly allow negation in the language? Allowing role conjunction only in role assertions is more puzzling. The only possible explanation is that conjunction behaves differently when used within an assertion than when "implicitly" used on the level of assertions - but could this not lead to unintuitive behaviour? Even on the level of concepts, I would usually assume 
 to express the same as 
. The other question is of course what makes conjunction on role assertions so relevant that they deserve this special treatment, or whether one could not simply leave them out. All this is not clear, and could have been better explained in the paper (the authors have a chance in the rebuttal of course). At the same time, the paper wastes space at other places when it discusses the complexity results - these results follow rather straight-forwardly and do not deserve a whole column in the main text.

What is more crucial with the current version of the paper are severe technical issues. The proof for the central Lemma 2 , which is needed to show that the translations are faithful does not work: my guess is that a lemma has been removed from the text before submission, but in its current state the correctness of the result cannot be established, and thus the paper not accepted. But already the definitions of the translations have problems, because they do not handle complex concepts, which would be sufficient to justify a reject. There are some further formal issues in the paper that are listed below in the detailed comments.

Detailed comments
Title: having "neuro-symbolic reasoning" in the title is a bit misleading, since apart from the motivation in the main text it does not play a central role in the paper

Introduction: "lack of sufficient information" - the open-world assumption of the DLs should already take care of this aspect

Background

"
-formula" - "axiom" is more common. Later they are called "sentences", but this terminology is not introduced
what is the "concept gammer"?
"composed of 1) An ABox [..] 2) A TBox" - should not be capitalized in the middle of the sentence
Definition 4: you formalization requires 
Definition 8 could benefit from some intuition on what is happening there
notation 
 is introduced after it has already been used in Def. 8
Definition 8: is it problematic to treat the implicit conjunction in knowledge bases as in the classical case then using the special conjunction operators when defining satisfaction of knowledge bases?
"classical versions >in< Definitions 5 [..]"
Translation Framework

Definition 16: this is broken: what happens with complex concepts? Your definition text requires 
, 
 to be atomic concepts, but what would then happen to axioms such as 
 or 
? Definition 17 has the same problem.
Proof of Lemma 2:
What is 
? Lemma 1 does not define such an interpretation (it defines 
), and neither do you. 
 also does not work, because 
 does not assign truth value 
left-to-right direction also does not handle complex concepts in role assertions
references to Lemma 1 and Lemma 2 do not make sense (you are in Lemma 2!)
Corollary 1: 
 and 
 are not defined
Lemma 4: because I cannot understand the corrolaries due to missing definitions, I cannot verify this lemma either.
Definition 18: "primitive concept" not defined - do you mean "atomic"?
Specific Points of Feedback for Rebuttal:
What is the motivation behind restricting role conjunction to role assertions? what are they useful for?
What is the motivation for not allowing negations? Can they not easily be simulated?
How would you handle complex concepts in GCIs and ABox assertions in your translation?
How would you fix the proof for Lemma 2? What does the missing lemma state?
Rating: 3: Clear rejection
Confidence: 5: The reviewer is absolutely certain that the evaluation is correct and very familiar with the relevant literature

# Review 2

Paper Summary:
This paper studies reasoning in the weak-Kleene-based description logics ALCH_AC and ALCH_S*. Its goal is to reduce reasoning in these non-classical logics to classical description-logic reasoning, thereby enabling the reuse of existing DL reasoners. The construction proceeds in two stages: ● First, weak-Kleene reasoning in ALCH+cap_wK is translated into classical ALCH+cap using parallel translations tau and mu, intended to encode truth and meaningfulness. ● Second, bilateral AC reasoning is decomposed through positive and negative translations pi and nu. ● For S*, additional "Daniels emulation" axioms are introduced to exclude unwanted nine-valued interpretations. The paper claims: ● soundness and completeness of the composed translations; ● linear translation time; ● PSPACE-complete entailment for empty or acyclic TBoxes; ● EXPTIME-complete entailment for general TBoxes.

Strengths:
● Relevant reasoning problem. Reusing mature classical DL reasoners for non-classical and paraconsistent DLs is a useful objective. The loan example clearly illustrates why classical explosion is undesirable for information aggregated from heterogeneous sources. ● Conceptually appealing decomposition. Separating truth and meaningfulness using the tau and mu translations, followed by separating verification and falsification through pi and nu, is an elegant and potentially reusable strategy. ● Modular presentation. The paper introduces the classical, weak-Kleene, AC, and S* semantics before presenting the translations. Definitions 16–18 make the intended construction reasonably easy to follow. ● Potential practical relevance. A faithful linear-size translation could provide an attractive alternative to implementing specialized non-classical reasoners from scratch. ● Appropriate theoretical focus. The absence of computational experiments is not by itself a weakness for this type of theoretical KRR paper. The manuscript is visually well formatted and generally follows the AAAI template.

Weaknesses:
Lemma 1 is false as stated — a fundamental flaw in the main proof chain Consider the permitted sentence phi = a:bottom . Definition 11 requires every weak-Kleene interpretation I to satisfy I(a:bottom) = f . Therefore I(phi) != e , and Lemma 1 claims that I*(phi) = t . However, if I* is itself a weak-Kleene interpretation, Definition 11 requires I*(a:bottom) = f . The induction proof considers atomic concepts but overlooks the constants top and bottom. Since Lemma 1 is used to prove Lemma 2, this problem affects the central translation argument.
Lemma 2 also has a direct counterexample under the paper's definitions Let the knowledge base be: ● K = <empty TBox, {a:bottom}> and let the query be phi = a:A , where A is a fresh atomic concept. This knowledge base has no weak-Kleene model. Consequently, according to Definition 6, K |=_wK phi holds vacuously. On the right-hand side of Lemma 2: ● K^tau contains a:bottom , so it classically entails phi^tau . ● K^mu contains only a:top , which does not entail a:A^mu . Therefore, the conjunction on the right-hand side of Lemma 2 is false, although its left-hand side is true. The composed translations might be repairable because the pi translation maps some problematic constants to fresh atoms. However, the general Lemma 2 used in the proof of Theorem 3 is false. The paper does not state or prove the restricted version that would be required.
Several central statements are not well typed or sufficiently formalized In Lemma 3, I is declared to be an ALCH_AC interpretation, but I(phi^pi) belongs to an enriched weak-Kleene language containing copied symbols. Corollary 1 appears to introduce the intended associated interpretation I_circle , but this makes the statement of Lemma 3 itself type-inconsistent. A similar ambiguity occurs in Lemma 5. An unspecified interpretation satisfying the classical Daniels axioms is subsequently used to evaluate source-language formulas as values in V3^2* . The mappings between the classical, weak-Kleene, AC, and S* interpretations must be stated explicitly.
Blank nodes are not part of the formally defined target logic Definition 16 uses assertions such as _:C^mu and D^mu and role assertions containing anonymous endpoints. However, Definitions 1–4 define ABoxes using individual names from N_I , and the paper does not add a model-theoretic semantics for blank nodes. The paper should specify: ● Whether every blank-node occurrence introduces a fresh existential individual. ● Whether different occurrences may share witnesses. ● How blank nodes are compiled into a standard ALCH+cap knowledge base. ● Whether the intended classical reasoners support the resulting representation. Without this information, the claim that standard DL reasoners can directly process the translation is not established.
The PSPACE/EXPTIME completeness claim in Theorem 7 is insufficiently proved Lemma 8 concerns a positive target language without concept complement. The cited standard complexity results for ALC and ALCH do not automatically establish the same lower bounds for this restricted Boolean fragment. The statement that complement "can be emulated with a finite number of other constructors" is not accompanied by a formal reduction. This requires particular care because satisfiability, subsumption, and entailment are not automatically interreducible when Boolean operators are restricted. A directly relevant reference is: A. Meier and T. Schneider. "Generalized Satisfiability for the Description Logic ALC." Theoretical Computer Science,
Moreover, even if Lemma 8 were established, Theorems 3 and 4 reduce non-classical entailment to classical entailment. Such a reduction provides an upper bound for the non-classical reasoning problems, but it does not establish PSPACE- hardness or EXPTIME-hardness. Theorem 7 therefore requires either a reduction in the opposite direction or an independently proved hard fragment. 6. The implementation and neuro-symbolic claims are stronger than the evidence ● No translation algorithm, reasoner-compatible serialization, or complete end-to-end example is supplied. ● The paper also does not integrate an LLM or evaluate a neuro-symbolic system. It presents a logical translation motivated by neuro-symbolic applications. The title and discussion should distinguish the proved logical contribution from its anticipated application to neuro-symbolic reasoning. 7. The reproducibility checklist overstates proof completeness The checklist answers "yes" to the inclusion of proofs for all novel claims. However, several central results are supported only by very short proof sketches, and the counterexamples above show that the current arguments do not prove the stated general results. The relevant checklist answer should be "partial" unless complete corrected proofs are added.

Justification of Recommendation:
The paper contains an appealing high-level idea and addresses a useful problem. Decomposing bilateral weak-Kleene semantics into classical copies for truth, meaningfulness, verification, and falsification could become a valuable technique. My rejection recommendation is driven by correctness rather than by the absence of experiments. Lemma 1 and Lemma 2, which support the main faithful-translation theorem, are false under the definitions currently given. The S* construction also contains unresolved interpretation-type issues, and Theorem 7 does not provide the reductions required for its hardness claims. Some intended results may remain true after restricting the intermediate lemmas and rebuilding the proofs. However, that would require a substantial theoretical revision rather than a minor clarification. I would rate a revised version higher if it provided: ● Correctly typed translations and interpretations. ● A sound treatment of constants and knowledge bases without models. ● A formal elimination or semantics of blank nodes. ● Independent proofs of the claimed complexity lower bounds. ● A reasoner-compatible example demonstrating the complete translation.

Specific Points of Feedback for Rebuttal:
Is a:bottom intended to be excluded from Lemma 1? If not, how does Lemma 1 avoid the counterexample phi = a:bottom ? 2 . How does Lemma 2 handle the knowledge base K = <empty TBox, {a:bottom}> ? 3 . If Lemma 2 is intended to apply only to formulas in the image of the pi translation, please state the exact restriction and explain why it suffices for Theorems 3 and 4. 4 . What are the formal semantics and freshness rules for the blank nodes in Definition 16? 5 . Can the blank nodes be replaced with fresh named individuals while preserving the claimed equivalence? 6 . What reduction establishes the PSPACE and EXPTIME lower bounds in Theorem 7? The presented translations appear to establish only upper bounds for the non-classical entailment problems. 7 . Please clarify the interpretation types used in Lemmas 3 and 5. In particular, which interpretation evaluates phi^pi , and how is a classical model of the Daniels axioms converted into an S* interpretation?
Rating: 3: Clear rejection
Confidence: 4: The reviewer is confident but not absolutely certain that the evaluation is correct

# AI Review 

AI Review
AI Reviewby AI Reviewer ()27 Jul 2026, 07:59 (modified: 24 Sept 2026, 17:53)Program Chairs, AI Reviewer, Area Chairs, Senior Program Committee, Authors, Program Committee SubmittedRevisions
Review:
Title: From Weak Kleene to Classical Description Logics: Faithful Translations for Neuro-Symbolic Reasoning

Synopsis of the paper
The paper studies reasoning in bilateral description logics designed to represent inconsistent and semantically indeterminate information. It proposes a compositional translation through an intermediate weak-Kleene logic into a classical description logic, with the goal of enabling existing reasoning infrastructure. The paper also derives translation-time and entailment-complexity claims and discusses applications to language-model-grounded reasoning.

Summary of Review
The paper addresses the concrete problem of reusing mature classical description-logic infrastructure for weak-Kleene bilateral reasoning. Its treatment of role restrictions and hierarchies extends the intended scope beyond atomic neuro-symbolic factuality judgments. However, a direct counterexample falsifies the central intermediate faithfulness lemma and consequently the main translation theorem. The five-valued encoding and claimed target language have additional formal problems, while the exact complexity classifications and novelty positioning are not established by the presented arguments.

Strengths

The loan example in “A Motivating Example” clearly isolates the intended failure of classical explosion. It shows how conflicting evidence about an account should coexist without supporting unrelated conclusions, concretely motivating paraconsistent reasoning for aggregated information.

Definitions 7–14 separate weak-Kleene operations, restricted quantifiers, bilateral values, satisfaction, and entailment. This organization makes the intended roles of meaningfulness, support, and refutation traceable across the three semantic layers.

The Discussion identifies semantic design choices beyond selecting a truth-value set. Its comparison of Nelsonian and alternative treatments of negated conditionals is relevant because these choices determine how verification and falsification propagate through role restrictions in more expressive extensions.

Weaknesses

The central faithfulness claim in Lemma 2 is false. For 
 and query 
, Definition 8 forces 
 in every source model, but Definition 16 gives 
, which can use another witness while falsifying 
. Theorem 3 follows by chaining Lemmas 2 and 4, so this counterexample also defeats the main reduction.

Lemma 1’s invariant fails for restricted universal quantification. If the input pairs are 
, Definition 8 evaluates the universal as 
; after applying 
 atomically, they become 
 and the universal remains 
, although Lemma 1 predicts 
 because the original value was not 
. This invalidates the model-conversion step used in Lemma 2.

Definition 18 does not enforce the five-valued range claimed in Lemma 5. Under Lemma 2’s own decoding, a classical assignment with 
 satisfies the meaningfulness equivalence but decodes to the excluded value 
. Thus, the stated Daniels axioms do not establish the model restriction required by Theorem 4.

Definition 16 produces expressions outside the target syntax of Definitions 1–3. Terms such as 
 and \langle_,_\rangle:r^\mu\sqcap s^\mu
 use blank nodes, but the target language defines assertions only over named individuals and gives no blank-node semantics. Under the usual existential reading, these are not ordinary assertion-entailment problems, so the claimed reduction to standard classical-DL reasoning requires an additional formal reduction.

The completeness classifications in Theorem 7 do not follow from the stated reductions. A linear reduction from the proposed logics to a classical target establishes upper bounds, but the proof supplies neither reverse reductions nor independent PSPACE-hardness and EXPTIME-hardness arguments. The exact lower bounds therefore remain unsupported even apart from the failed faithfulness result.

The novelty discussion omits closely related work on compilation into classical DL reasoning. Bienvenu, Bourgaux, and Kozhemiachenko (2026), which appears nowhere in the supplied manuscript, reduce positive/negative paraconsistent DL query answering to classical query answering and derive complexity results. Their four-valued semantics and query task differ from weak-Kleene entailment, but this comparison is necessary to delimit the novelty of the compilation paradigm.

Suggestions for Improvement

A source–target diagram before Definition 16 could identify the type and purpose of each translation 
, 
, 
, and 
, explain why multiple classical checks are introduced, and show where the five-valued restriction enters. This would reduce the substantial reconstruction currently required from readers.

Reusing the loan example for one complete translated query would connect the formal machinery to the motivating application. Showing the generated classical knowledge base and intended reasoner calls would also clarify the distinction among entailment, satisfiability, and existential query answering.

An exhaustive finite-model test suite over small domains and all constructors would provide a useful validation layer for a revised construction. Comparing source evaluations with decoded target evaluations would expose failures involving universal restrictions, meaningfulness witnesses, constants, and bilateral coherence.

The conclusion could distinguish established metatheoretic results from prospective practical consequences. Implementation in an existing reasoner, preservation of its optimizations, and benefits for full neuro-symbolic pipelines are separate questions from the existence of a formal reduction.

Additional Details and Minor Issues

Lemma 3 equates bilateral 
 with weak-Kleene 
, although these have different codomains; the intended statement likely concerns 
 under 
.

Definition 18 uses role equivalence, while Definition 2 introduces only role inclusion. Two inclusions could encode the intended construct.

Definition 6 omits the queried formula after its entailment notation, and Definition 14 changes the logic subscript from the role-hierarchy language to the language without it.

The motivating example alternates between SecureAcc and SecuredAcc, changing the predicate in the claimed explosive conclusion.

The theorem numbering begins with Theorem 3 and later jumps to Theorem 7, complicating cross-reference.

References

Bienvenu, M., Bourgaux, C., & Kozhemiachenko, D. (2026). Queries with exact truth values on concept and role atoms in paraconsistent description logics. Journal of Artificial Intelligence Research, 85, Article 19. doi:10.1613/jair.1.18676.