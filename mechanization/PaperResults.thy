theory PaperResults
  imports Loops SyntacticAssertions Compositionality TotalLogic ExamplesCompositionality
begin

text \<open>This file contains the results mentioned the paper. It is organized in the same order and with
the same structure as the paper. You can use the panel "Sidekick" on the right to see and navigate
the structure of the file, via sections and subsections.
You can ctrl+click on terms to jump to their definition.\<close>

section \<open>3: Hyper Hoare Logic\<close>

subsection \<open>3.1: Language and Semantics\<close>

text \<open>The programming language is defined in the file Language.thy:
- The type of program state is \<^typ>\<open>('pvar, 'pval) pstate\<close> (<-- you can ctrl+click on the name pstate to jump to its definition).
- Program commands are defined as the type \<^typ>\<open>('var, 'val) stmt\<close>.
- The big-step semantics is defined as \<^const>\<open>single_sem\<close>. We also use the notation \<^term>\<open>\<langle>C, \<sigma>\<rangle> \<rightarrow> \<sigma>'\<close>.\<close>

subsection \<open>3.2: Hyper-Triples, Formally\<close>

text \<open>
- Extended states (definition 2) are defined as \<^typ>\<open>('lvar, 'lval, 'pvar, 'pval) state\<close>.
- Hyper-assertions (definition 3) are defined in the file Logic.thy as \<^typ>\<open>('lvar, 'lval, 'pvar, 'pval) state hyperassertion\<close>.
- The extended semantics (definition 4) is defined in the file Language.thy as \<^const>\<open>sem\<close>.
- Lemma 1 is shown and proven below.
- Hyper-triples (definition 5) are defined in the file Logic.thy as \<^const>\<open>hyper_hoare_triple\<close>. We
  also use the notation \<^term>\<open>\<Turnstile> {P} C {Q}\<close>.\<close>

lemma lemma1:
  "sem C (S1 \<union> S2) = sem C S1 \<union> sem C S2"
  "S \<subseteq> S' \<Longrightarrow> sem C S \<subseteq> sem C S'"
  "sem C (\<Union>x. f x) = (\<Union>x. sem C (f x))"
  "sem Skip S = S"
  "sem (C1;; C2) S = sem C2 (sem C1 S)"
  "sem (If C1 C2) S = sem C1 S \<union> sem C2 S"
  "sem (While C) S = (\<Union>n. iterate_sem n C S)"
  using sem_if sem_seq sem_union sem_skip sem_union_general sem_monotonic sem_while by metis+

subsection \<open>3.3: Core Rules\<close>

text \<open>The core rules are defined in the file Logic.thy, as \<^const>\<open>syntactic_HHT\<close>. We also use the
notation \<^term>\<open>\<turnstile> {P} C {Q}\<close>. Operators \<otimes> (definition 6) and \<Otimes> (definition 7) are defined as
\<^const>\<open>join\<close> and \<^const>\<open>natural_partition\<close>, respectively.\<close>

subsection \<open>3.4: Soundness and Completeness\<close>

theorem thm1_soundness:
  assumes "\<turnstile> {P} C {Q}"
  shows "\<Turnstile> {P} C {Q}"
  using assms soundness by auto

theorem thm2_completeness:
  assumes "\<Turnstile> {P} C {Q}"
  shows "\<turnstile> {P} C {Q}"
  using assms completeness by auto

subsection \<open>3.5: Expressivity of Hyper-Triples\<close>

text \<open>Program hyperproperties (definition 8) are defined in the file ProgramHyperproperties as
\<^typ>\<open>('pvar, 'pval) program_hyperproperty\<close>, and the satisfiability of program hyperproperties is
defined via the function \<^const>\<open>hypersat\<close>.\<close>

theorem thm3_expressing_hyperproperties_as_hyper_triples:
  fixes to_lvar :: "'pvar \<Rightarrow> 'lvar"
  fixes to_lval :: "'pval \<Rightarrow> 'lval"
  fixes H :: "('pvar, 'pval) program_hyperproperty"
  assumes "injective to_lvar" \<comment>\<open>The cardinality of 'lvar is at least the cardinality of 'pvar.\<close>
      and "injective to_lval" \<comment>\<open>The cardinality of 'lval is at least the cardinality of 'pval.\<close>
    shows "\<exists>P Q::('lvar, 'lval, 'pvar, 'pval) state hyperassertion. (\<forall>C. hypersat C H \<longleftrightarrow> \<Turnstile> {P} C {Q})"
  using assms proving_hyperproperties
  by blast

theorem thm4_disproving_triples:
  "\<not> \<Turnstile> {P} C {Q} \<longleftrightarrow> (\<exists>P'. sat P' \<and> entails P' P \<and> \<Turnstile> {P'} C {\<lambda>S. \<not> Q S})"
  using disproving_triple by auto



section \<open>4: Syntactic Rules\<close>

subsection \<open>4.1: Syntactic Hyper-Assertions\<close>

text \<open>Syntactic hyper-expressions and hyper-assertions (definition 9) are defined in the file
SyntacticAssertions.thy as \<^typ>\<open>'val exp\<close> and \<^typ>\<open>'val assertion\<close> respectively, where 'val is the
type of both logical and program values. Note that we use de Bruijn indices (i.e, natural numbers)
for quantified states and variables.\<close>

subsection \<open>4.2: Syntactic Rules for Deterministic and Non-Deterministic Assignments.\<close>

text \<open>We prove semantic versions of the syntactic rules from section 4 (figure 4).
We use \<^const>\<open>interp_assert\<close> to convert a syntactic hyper-assertion into a semantic one, because
our hyper-triples require semantic hyper-assertions. Similarly, we use \<^const>\<open>interp_pexp\<close> to convert
a syntactic program expression into a semantic one.
\<^term>\<open>transform_assign x pe P\<close> and \<^term>\<open>transform_havoc x P\<close> correspond to A^e_x and H_x from definition 10.\<close>

proposition AssignS:
  "\<Turnstile> { interp_assert (transform_assign x pe P) } Assign x (interp_pexp pe) {interp_assert P}"
  using rule_assign_syntactic by auto

proposition HavocS:
  "\<Turnstile> { interp_assert (transform_havoc x P) } Havoc x {interp_assert P}"
  using rule_havoc_syntactic by auto

subsection \<open>4.3: Syntactic Rules for Assume Statements\<close>

text \<open>\<^const>\<open>transform_assume\<close> corresponds to \<Pi>_p (definition 11). As before, we use \<^const>\<open>interp_pbexp\<close>
to convert a syntactic program boolean expression into a semantic one.
Similarly, \<^term>\<open>pbexp_to_assertion 0 pb\<close> converts the syntactic program boolean expression pb into
a syntactic hyper-assertion, which applies to the state 0 (recall that we use de Bruijn indices,
and thus state "0" corresponds to the closest quantified state.\<close>

proposition AssumeS:
  "\<Turnstile> { interp_assert (transform_assume (pbexp_to_assertion 0 pb) P) } Assume (interp_pbexp pb) {interp_assert P}"
  using rule_assume_syntactic by auto

section \<open>5: Proof Principles for Loops\<close>

text \<open>We show in the following our proof rules for loops, presented in figure 6. These use the following constructs:
- \<^term>\<open>natural_partition I\<close> corresponds to the \<Otimes> operator from definition 7.
- \<^term>\<open>lnot b\<close> negates b.
- \<^term>\<open>while_cond b C\<close> is defined as \<^term>\<open>While (Assume b;; C);; Assume (lnot b)\<close>.\<close>

theorem while_desugared:
  assumes "\<And>n. \<Turnstile> {I n} Assume b;; C {I (Suc n)}"
      and "\<Turnstile> { natural_partition I } Assume (lnot b) { Q }"
    shows "\<Turnstile> {I 0} while_cond b C { Q }"
  by (metis assms(1) assms(2) seq_rule while_cond_def while_rule)

subsection \<open>5.1: Synchronized Control Flow\<close>

text \<open>In the following:
- \<^term>\<open>conj A B\<close> corresponds to the hyper-assertion \<open>A \<and> B\<close>.
- \<^term>\<open>holds_forall b\<close> corresponds to \<open>\<box>b\<close>.
- \<^term>\<open>low_exp b\<close> corresponds to \<open>low(b)\<close>.
- \<^term>\<open>disj A B\<close> corresponds to the hyper-assertion \<open>A \<or> B\<close>.
- \<^term>\<open>emp\<close> checks whether the set of states is empty.
- \<^term>\<open>if_then_else b C1 C2\<close> is syntactic sugar for \<^term>\<open>If (Assume b;; C1) (Assume (lnot b);; C2)\<close>.\<close>

theorem WhileSync:
  assumes "\<Turnstile> {conj I (holds_forall b)} C {conj I (low_exp b)}"
  shows "\<Turnstile> {conj I (low_exp b)} while_cond b C {conj (disj I emp) (holds_forall (lnot b))}"
  using assms while_synchronized[of "\<lambda>n. I"]
  by (simp add: disj_def Loops.exists_def conj_def hyper_hoare_triple_def)

theorem IfSync:
  assumes "\<Turnstile> {conj P (holds_forall b)} C1 {Q}"
      and "\<Turnstile> {conj P (holds_forall (lnot b))} C2 {Q}"
    shows "\<Turnstile> {conj P (low_exp b)} if_then_else b C1 C2 {Q}"
  using assms(1) assms(2) if_synchronized by blast

subsection \<open>5.2: \<forall>*\<exists>*-Hyperproperties\<close>

text \<open>In the following:
- \<^term>\<open>if_then b C\<close> is syntactic sugar for \<^term>\<open>If (Assume b;; C) (Assume (lnot b))\<close>.
- \<^term>\<open>no_forall_state_after_existential Q\<close> holds iff there is no universal state quantifier \<forall>\<langle>_\<rangle> after any \<exists> in Q.\<close>

theorem while_forall_exists:
  assumes "\<Turnstile> {I} if_then b C {I}"
      and "\<Turnstile> {I} Assume (lnot b) {interp_assert Q}"
      and "no_forall_state_after_existential Q"
    shows "\<Turnstile> {I} while_cond b C {conj (interp_assert Q) (holds_forall (lnot b))}"
  using while_general_syntactic[of "\<lambda>n. I"] assms
  by blast

subsection \<open>5.3: \<exists>*\<forall>*-Hyperproperties\<close>

text \<open>\<^term>\<open>wfP lt\<close> in the following rule ensures that the binary operator \<open>lt\<close> is well-founded.
\<open>e\<close> is a function of a program state, which must decrease after each iteration.\<close>

theorem while_loop_exists:
  assumes "wfP lt"
      and "\<And>v. \<Turnstile> { (\<lambda>S. \<exists>\<phi>\<in>S. e (snd \<phi>) = v \<and> b (snd \<phi>) \<and> P \<phi> S) } if_then b C { (\<lambda>S. \<exists>\<phi>\<in>S. lt (e (snd \<phi>)) v \<and> P \<phi> S) }"
      and "\<And>\<phi>. \<Turnstile> { P \<phi> } while_cond b C { Q \<phi> }"
    shows "\<Turnstile> { (\<lambda>S. \<exists>\<phi>\<in>S. P \<phi> S) } while_cond b C { (\<lambda>S. \<exists>\<phi>\<in>S. Q \<phi> S)}"
  using exists_terminates_loop assms by blast



section \<open>Appendix A: Technical Definitions Omitted from the Paper\<close>

text \<open>The following definitions are formalized in the file SyntacticAssertions.thy:
- Evaluation of hyper-expressions (definition 12): \<^const>\<open>interp_exp\<close>.
- Satisfiability of hyper-assertions (definition 12): \<^const>\<open>sat_assertion\<close>.
- Syntactic transformation for deterministic assignments (definition 13): \<^const>\<open>transform_assign\<close>.
- Syntactic transformation for non-deterministic assignments (definition 14): \<^const>\<open>transform_havoc\<close>.
- Syntactic transformation for assume statements. (definition 15): \<^const>\<open>transform_assume\<close>.\<close>


section \<open>Appendix C: Expressing Judgments of Hoare Logics as Hyper-Triples\<close>

subsection \<open>Appendix C.1: Overapproximate Hoare Logics\<close>

text \<open>The following judgments are defined in the file Expressivity.thy as follows:
- Definition 16 (Hoare Logic): \<^term>\<open>HL P C Q\<close>.
- Definition 17 (Cartesian Hoare Logic): \<^term>\<open>CHL P C Q\<close>.\<close>

proposition prop_1_HL_expresses_hyperproperties:
  "\<exists>H. (\<forall>C. hypersat C H \<longleftrightarrow> HL P C Q) \<and> k_hypersafety 1 H"
  using HL_expresses_hyperproperties by blast

proposition prop_2_expressing_HL_in_HHL:
  "HL P C Q \<longleftrightarrow> (hyper_hoare_triple (over_approx P) C (over_approx Q))"
  using encoding_HL by auto

proposition prop_3_CHL_is_hyperproperty:
  "hypersat C (CHL_hyperprop P Q) \<longleftrightarrow> CHL P C Q"
  using CHL_hyperproperty by fast

proposition prop_4_encoding_CHL_in_HHL:
  assumes "not_free_var_of P x"
      and "not_free_var_of Q x"
      and "injective from_nat"
    shows "CHL P C Q \<longleftrightarrow> \<Turnstile> {encode_CHL from_nat x P} C {encode_CHL from_nat x Q}"
  using encoding_CHL assms by fast



subsection \<open>Appendix C.2: Underapproximate Hoare Logics\<close>

text \<open>The following judgments are defined in the file Expressivity.thy as follows:
- Definition 18 (Incorrectness Logic): \<^term>\<open>IL P C Q\<close>.
- Definition 19 (k-Incorrectness Logic): \<^term>\<open>RIL P C Q\<close>.
- Definition 20 (Forward Underapproximation): \<^term>\<open>FU P C Q\<close>.
- Definition 21 (k-Forward Underapproximation): \<^term>\<open>RFU P C Q\<close>.\<close>

text \<open>RIL is the old name of k-IL, and RFU is the old name of k-FU.\<close>

proposition prop_5_IL_hyperproperties:
  "IL P C Q \<longleftrightarrow> IL_hyperprop P Q (set_of_traces C)"
  using IL_expresses_hyperproperties by fast

proposition prop_6_expressing_IL_in_HHL:
  "IL P C Q \<longleftrightarrow> (hyper_hoare_triple (under_approx P) C (under_approx Q))"
  using encoding_IL by fast

proposition prop_7_kIL_hyperproperties:
  "hypersat C (RIL_hyperprop P Q) \<longleftrightarrow> RIL P C Q"
  using RIL_expresses_hyperproperties by fast

proposition prop_8_expressing_kIL_in_HHL:
  fixes x :: "'lvar"
  assumes "\<And>l l' \<sigma>. (\<lambda>i. (l i, \<sigma> i)) \<in> P \<longleftrightarrow> (\<lambda>i. (l' i, \<sigma> i)) \<in> P"  (* P does not depend on logical variables *)
      and "injective (indexify :: (('a \<Rightarrow> ('pvar \<Rightarrow> 'pval)) \<Rightarrow> 'lval))" (* |lval| \<ge> |PStates^k| *)
      and "c \<noteq> x"
      and "injective from_nat"
      and "not_free_var_of (P :: ('a \<Rightarrow> ('lvar \<Rightarrow> 'lval) \<times> ('pvar \<Rightarrow> 'pval)) set) x \<and> not_free_var_of P c"
      and "not_free_var_of Q x \<and> not_free_var_of Q c"
    shows "RIL P C Q \<longleftrightarrow> \<Turnstile> {pre_insec from_nat x c P} C {post_insec from_nat x c Q}"
  using assms(1) assms(2) assms(3) assms(4) assms(5) assms(6) by (rule encoding_RIL)

proposition FU_hyperproperties:
  "hypersat C (hyperprop_FU P Q) \<longleftrightarrow> FU P C Q"
  by (rule FU_expresses_hyperproperties)

proposition prop_9_expressing_FU_in_HHL:
  "FU P C Q \<longleftrightarrow> \<Turnstile> {encode_FU P} C {encode_FU Q}"
  by (rule encoding_FU)

proposition prop_10_kFU_expresses_hyperproperties:
  "hypersat C (RFU_hyperprop P Q) \<longleftrightarrow> RFU P C Q"
  by (rule RFU_captures_hyperproperties)

proposition prop_11_encode_kFU_in_HHL:
  assumes "not_free_var_of P x"
      and "not_free_var_of Q x"
      and "injective from_nat"
    shows "RFU P C Q \<longleftrightarrow> \<Turnstile> {encode_RFU from_nat x P} C {encode_RFU from_nat x Q}"
  using assms
  by (rule encode_RFU)

subsection \<open>Appendix C.3: Beyond Over- and Underapproximation\<close>

text \<open>The following judgment is defined in the file Expressivity.thy as follows:
- Definition 22 (k-Universal Existential): \<^term>\<open>RUE P C Q\<close>.
Note that RUE is the old name of k-UE.\<close>

proposition prop_12_kUE_expresses_hyperproperty:
  "RUE P C Q \<longleftrightarrow> hypersat C (hyperprop_RUE P Q)"
  by (rule RUE_express_hyperproperties)


proposition prop_13_expressing_kUE_in_HHL:
  assumes "injective fn \<and> injective fn1 \<and> injective fn2"
      and "t \<noteq> x"
      and "injective (fn :: nat \<Rightarrow> 'a)"
      and "injective fn1"
      and "injective fn2"
      and "not_in_free_vars_double {x, t} P"
      and "not_in_free_vars_double {x, t} Q"
  shows "RUE P C Q \<longleftrightarrow> \<Turnstile> {encode_RUE_1 fn fn1 fn2 x t P} C {encode_RUE_2 fn fn1 fn2 x t Q}"
  using assms by (rule encoding_RUE)


text \<open>Example 3\<close>
proposition proving_refinement:
  fixes P :: "(('lvar \<Rightarrow> 'lval) \<times> ('pvar \<Rightarrow> 'pval)) set \<Rightarrow> bool"
  assumes "(a :: 'pval) \<noteq> b"
    (* and x free var *)
      and "P = (\<lambda>S. card S = 1)"
      and "Q = (\<lambda>S.
  \<forall>\<phi>\<in>S. snd \<phi> x = a \<longrightarrow> (fst \<phi>, (snd \<phi>)(x := b)) \<in> S)"
      and "not_free_var_stmt x C1"
      and "not_free_var_stmt x C2"
  shows "refinement C1 C2 \<longleftrightarrow>
  \<Turnstile> { P } If (Seq (Assign (x :: 'pvar) (\<lambda>_. a)) C1) (Seq (Assign x (\<lambda>_. b)) C2) { Q }"
  using assms
  by (rule encoding_refinement)








section \<open>Appendix D: Compositionality\<close>

subsection \<open>Appendix D.1: Compositionality Rules\<close>

text \<open>In the following, we show the rules from figure 11, in the order in which they appear.\<close>

proposition rule_Linking:
  assumes "\<And>\<phi>1 (\<phi>2 :: ('a, 'b, 'c, 'd) state). fst \<phi>1 = fst \<phi>2 \<and> ( \<Turnstile> { (in_set \<phi>1 :: (('a, 'b, 'c, 'd) state) hyperassertion) } C { in_set \<phi>2 } )
  \<Longrightarrow> ( \<Turnstile> { (P \<phi>1 :: (('a, 'b, 'c, 'd) state) hyperassertion) } C { Q \<phi>2 } )"
  shows "\<Turnstile> { ((\<lambda>S. \<forall>\<phi>1 \<in> S. P \<phi>1 S) :: (('a, 'b, 'c, 'd) state) hyperassertion) } C { (\<lambda>S. \<forall>\<phi>2 \<in> S. Q \<phi>2 S) }"
  using assms by (rule rule_linking)

proposition rule_And:
  assumes "\<Turnstile> {P} C {Q}"
      and "\<Turnstile> {P'} C {Q'}"
    shows "\<Turnstile> {conj P P'} C {conj Q Q'}"
  using assms by (rule rule_And)

proposition rule_Or:
  assumes "\<Turnstile> {P} C {Q}"
      and "\<Turnstile> {P'} C {Q'}"
    shows "\<Turnstile> {disj P P'} C {disj Q Q'}"
  using assms by (rule rule_Or)

proposition rule_FrameSafe:
  assumes "wr C \<inter> fv F = {}"
      and "wf_assertion F"
      and "no_exists_state F"
    shows "\<Turnstile> {interp_assert F} C {interp_assert F}"
  using safe_frame_rule_syntactic assms by auto

proposition rule_Forall:
  assumes "\<And>x. \<Turnstile> {P x} C {Q x}"
  shows "\<Turnstile> {forall P} C {forall Q}"
  using assms by (rule rule_Forall)

proposition rule_IndexedUnion:
  assumes "\<And>x. \<Turnstile> {P x} C {Q x}"
  shows "\<Turnstile> {general_join P} C {general_join Q}"
  using assms by (rule rule_IndexedUnion)

proposition rule_Union:
  assumes "\<Turnstile> {P} C {Q}"
      and "\<Turnstile> {P'} C {Q'}"
    shows "\<Turnstile> {join P P'} C {join Q Q'}"
  using assms by (rule rule_Union)

proposition rule_BigUnion:
  fixes P :: "((('a \<Rightarrow> 'b) \<times> ('c \<Rightarrow> 'd)) set \<Rightarrow> bool)"
  assumes "\<Turnstile> {P} C {Q}"
  shows "\<Turnstile> {general_union P} C {general_union Q}"
  using assms by (rule rule_BigUnion)

proposition rule_Specialize:
  assumes "\<Turnstile> {interp_assert P} C {interp_assert Q}"
      and "indep_of_set b"
      and "wf_assertion_aux 0 1 b"
      and "wr C \<inter> fv b = {}"
    shows "\<Turnstile> { interp_assert (transform_assume b P) } C { interp_assert (transform_assume b Q) }"
  using filter_rule_syntactic assms by blast

text \<open>In the following, \<^term>\<open>entails_with_updates vars P P'\<close> and \<^term>\<open>invariant_on_updates vars Q\<close>
respectively correspond to the notions of entailments modulo logical variables and invariance with
respect to logical updates, as described in definition 23.\<close>

proposition rule_LUpdate:
  assumes "\<Turnstile> {P'} C {Q}"
      and "entails_with_updates vars P P'"
      and "invariant_on_updates vars Q"
    shows "\<Turnstile> {P} C {Q}"
  using assms by (rule rule_LUpdate)

proposition rule_LUpdateSyntactic:
  assumes "\<Turnstile> { (\<lambda>S. P S \<and> e_recorded_in_t e t S) } C { Q }"
      and "not_fv_hyper t P"
      and "not_fv_hyper t Q"
    shows "\<Turnstile> { P } C { Q }"
  using LUpdateS assms by fast

proposition rule_AtMost:
  assumes "\<Turnstile> {P} C {Q}"
  shows "\<Turnstile> {has_superset P} C {has_superset Q}"
  using assms by (rule rule_AtMost)

(* derived from join *)
proposition rule_AtLeast:
  assumes "\<Turnstile> {P} C {Q}"
  shows "\<Turnstile> {has_subset P} C {has_subset Q}"
  using assms by (rule rule_AtLeast)

proposition rule_True:
  "\<Turnstile> {P} C {\<lambda>_. True}"
  by (rule rule_True)

proposition rule_False:
  "\<Turnstile> { (\<lambda>_. False) } C {Q}"
  by (rule rule_False)

proposition rule_Empty:
  "\<Turnstile> { (\<lambda>S. S = {}) } C { (\<lambda>S. S = {}) }"
  by (rule rule_Empty)

subsection \<open>Appendix D.2: Examples\<close>


proposition fig_12_composing_monotonicity_and_minimum:
  fixes P :: "((('a \<Rightarrow> 'b) \<times> ('c \<Rightarrow> 'd)) set \<Rightarrow> bool)"
  fixes i :: 'a
  fixes x y :: 'c
  fixes leq :: "'d \<Rightarrow> 'd \<Rightarrow> bool"
  fixes one two :: 'b
  assumes "\<Turnstile> { P } C1 { has_minimum x leq }"
      and "\<Turnstile> { is_monotonic i x one two leq } C2 { is_monotonic i y one two leq }"
      and "\<Turnstile> { (is_singleton :: ((('a \<Rightarrow> 'b) \<times> ('c \<Rightarrow> 'd)) set \<Rightarrow> bool)) } C2 { is_singleton }"
      and "one \<noteq> two"
      and "\<And>x. leq x x" \<comment>\<open>reflexivity\<close>
    shows "\<Turnstile> { P } C1 ;; C2 { has_minimum y leq }"
  using assms by (rule composing_monotonicity_and_minimum)

proposition fig_13_composing_GNI_with_SNI:
  fixes h :: 'lvar
  fixes l :: 'pvar
  assumes "\<Turnstile> { (low l :: (('lvar, 'lval, 'pvar, 'pval) state) hyperassertion) } C2 { low l }"
      and "\<Turnstile> { (not_empty :: (('lvar, 'lval, 'pvar, 'pval) state) hyperassertion) } C2 { not_empty }"
      and "\<Turnstile> { (low l :: (('lvar, 'lval, 'pvar, 'pval) state) hyperassertion) } C1 { lGNI l h }"
    shows "\<Turnstile> { (low l :: (('lvar, 'lval, 'pvar, 'pval) state) hyperassertion) } C1;; C2 { lGNI l h }"
  using assms by (rule composing_GNI_with_SNI)




section \<open>Appendix E: Termination-Based Reasoning\<close>

text \<open>Total hyper-triples (definition 24) are defined as \<^const>\<open>total_hyper_triple\<close>, and usually
written \<^term>\<open>\<Turnstile>TOT {P} C {Q}\<close>.\<close>

theorem rule_Frame:
  assumes "\<Turnstile>TOT {P} C {Q}"
      and "wr C \<inter> fv F = {}"
      and "wf_assertion F"
    shows "\<Turnstile>TOT {conj P (interp_assert F)} C {conj Q (interp_assert F)}"
  by (simp add: assms(1) assms(2) assms(3) frame_rule_syntactic)

theorem rule_WhileSyncTot:
  assumes "wfP lt"
      and "\<And>n. not_fv_hyper t (I n)"
      and "\<And>n. \<Turnstile>TOT {conj (conj (I n) (holds_forall b)) (e_recorded_in_t e t)} C {conj (conj (I (Suc n)) (low_exp b)) (e_smaller_than_t e t lt)}"
    shows "\<Turnstile>TOT {conj (I 0) (low_exp b)} while_cond b C {conj (exists I) (holds_forall (lnot b))}"
  using assms while_synchronized_tot by meson



section \<open>Appendix H: Synchronous Reasoning over Different Branches\<close>

proposition prop_14_synchronized_if_rule:
  assumes "\<Turnstile> {P} C1 {P1}"
      and "\<Turnstile> {P} C2 {P2}"
      and "\<Turnstile> {combine from_nat x P1 P2} C {combine from_nat x R1 R2}"
      and "\<Turnstile> {R1} C1' {Q1}"
      and "\<Turnstile> {R2} C2' {Q2}"
      and "not_free_var_hyper x P1"
      and "not_free_var_hyper x P2"
      and "injective (from_nat :: nat \<Rightarrow> 'a)"
      and "not_free_var_hyper x R1"
      and "not_free_var_hyper x R2"
    shows "\<Turnstile> {P} If (Seq C1 (Seq C C1')) (Seq C2 (Seq C C2')) {join Q1 Q2}"
  using if_sync_rule assms by fast

end