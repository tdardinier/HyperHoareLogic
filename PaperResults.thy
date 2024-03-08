theory PaperResults
  imports Loops SyntacticAssertions Compositionality TotalLogic ExamplesCompositionality
begin

text \<open>This file contains the results mentioned the paper.\<close>

subsection \<open>Section 3\<close>

subsubsection \<open>Section 3.2\<close>

lemma lemma1:
  "sem C (S1 \<union> S2) = sem C S1 \<union> sem C S2"
  "S \<subseteq> S' \<Longrightarrow> sem C S \<subseteq> sem C S'"
  "sem C (\<Union>x. f x) = (\<Union>x. sem C (f x))"
  "sem Skip S = S"
  "sem (C1;; C2) S = sem C2 (sem C1 S)"
  "sem (If C1 C2) S = sem C1 S \<union> sem C2 S"
  "sem (While C) S = (\<Union>n. iterate_sem n C S)"
  using sem_if sem_seq sem_union sem_skip sem_union_general sem_monotonic sem_while by metis+

subsubsection \<open>Section 3.4\<close>

theorem thm1_soundness:
  assumes "\<turnstile> {A} C {B}"
  shows "\<Turnstile> {A} C {B}"
  using assms soundness by auto

theorem thm2_completeness:
  assumes "\<Turnstile> {A} C {B}"
  shows "\<turnstile> {A} C {B}"
  using assms completeness by auto

subsubsection \<open>Section 3.5\<close>

theorem expressing_hyperproperties_as_hyper_triples:
  fixes to_lvar :: "'pvar \<Rightarrow> 'lvar"
  fixes to_lval :: "'pval \<Rightarrow> 'lval"
  assumes "injective to_lvar"
      and "injective to_lval"
    shows "\<exists>P Q::('lvar, 'lval, 'pvar, 'pval) state hyperassertion. (\<forall>C. hypersat C H \<longleftrightarrow> \<Turnstile> {P} C {Q})"
  using assms proving_hyperproperties
  by blast

theorem thm4_disproving_triples:
  "\<not> \<Turnstile> {P} C {Q} \<longleftrightarrow> (\<exists>P'. sat P' \<and> entails P' P \<and> \<Turnstile> {P'} C {\<lambda>S. \<not> Q S})"
  using disproving_triple by auto







subsection \<open>Section 4\<close>

subsubsection \<open>Section 4.2\<close>

proposition AssignS:
  "\<Turnstile> { interp_assert (transform_assign x pe P) } Assign x (interp_pexp pe) {interp_assert P}"
  using rule_assign_syntactic by auto

proposition HavocS:
  "\<Turnstile> { interp_assert (transform_havoc x P) } Havoc x {interp_assert P}"
  using rule_havoc_syntactic by auto

subsubsection \<open>Section 4.3\<close>

proposition AssumeS:
  "\<Turnstile> { interp_assert (transform_assume (pbexp_to_assertion 0 pb) P) } Assume (interp_pbexp pb) {interp_assert P}"
  using rule_assume_syntactic by auto

subsection \<open>Section 5\<close>

theorem while_desugared:
  assumes "\<And>n. \<Turnstile> {I n} Assume b;; C {I (Suc n)}"
      and "\<Turnstile> { natural_partition I } Assume (lnot b) { Q }"
    shows "\<Turnstile> {I 0} while_cond b C { Q }"
  by (metis assms(1) assms(2) seq_rule while_cond_def while_rule)

subsubsection \<open>Section 5.1\<close>

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

subsubsection \<open>Section 5.2\<close>

theorem while_forall_exists:
  assumes "\<Turnstile> {I} if_then b C {I}"
      and "\<Turnstile> {I} Assume (lnot b) {interp_assert Q}"
      and "no_forall_state_after_existential Q"
    shows "\<Turnstile> {I} while_cond b C {conj (interp_assert Q) (holds_forall (lnot b))}"
  using while_general_syntactic[of "\<lambda>n. I"] assms
  by blast

subsubsection \<open>Section 5.3\<close>

theorem while_loop_exists:
  assumes "wfP lt"
      and "\<And>v. \<Turnstile> { (\<lambda>S. \<exists>\<phi>\<in>S. e (snd \<phi>) = v \<and> b (snd \<phi>) \<and> P \<phi> S) } if_then b C { (\<lambda>S. \<exists>\<phi>\<in>S. lt (e (snd \<phi>)) v \<and> P \<phi> S) }"
      and "\<And>\<phi>. \<Turnstile> { P \<phi> } while_cond b C { Q \<phi> }"
    shows "\<Turnstile> { (\<lambda>S. \<exists>\<phi>\<in>S. P \<phi> S) } while_cond b C { (\<lambda>S. \<exists>\<phi>\<in>S. Q \<phi> S)}"
  using exists_terminates_loop assms by blast




subsection \<open>Appendix C: Expressing Judgments of Hoare Logics as Hyper-Triples\<close>

theorem prop_HL_expresses_hyperproperties:
  "\<exists>H. (\<forall>C. hypersat C H \<longleftrightarrow> HL P C Q) \<and> k_hypersafety 1 H"
  using HL_expresses_hyperproperties by blast

theorem encoding_HL_in_HHL:
  "HL P C Q \<longleftrightarrow> (hyper_hoare_triple (over_approx P) C (over_approx Q))"
  using encoding_HL by auto

theorem encoding_CHL_in_HHL:
  assumes "not_free_var_of P x"
      and "not_free_var_of Q x"
      and "injective from_nat"
    shows "CHL P C Q \<longleftrightarrow> \<Turnstile> {encode_CHL from_nat x P} C {encode_CHL from_nat x Q}"
  using encoding_CHL assms by fast

theorem CHL_is_hyperproperty:
  "hypersat C (CHL_hyperprop P Q) \<longleftrightarrow> CHL P C Q"
  using CHL_hyperproperty by fast

lemma IL_hyperproperties:
  "IL P C Q \<longleftrightarrow> IL_hyperprop P Q (set_of_traces C)"
  using IL_expresses_hyperproperties by fast

theorem encoding_IL_in_HHL:
  "IL P C Q \<longleftrightarrow> (hyper_hoare_triple (under_approx P) C (under_approx Q))"
  using encoding_IL by fast

text \<open>RIL is the old name of k-IL\<close>
theorem kIL_hyperproperties:
  "hypersat C (RIL_hyperprop P Q) \<longleftrightarrow> RIL P C Q"
  using RIL_expresses_hyperproperties by fast

theorem encoding_RIL:
  fixes x :: "'lvar"
  assumes "\<And>l l' \<sigma>. (\<lambda>i. (l i, \<sigma> i)) \<in> P \<longleftrightarrow> (\<lambda>i. (l' i, \<sigma> i)) \<in> P"  (* P does not depend on logical variables *)
      and "injective (indexify :: (('a \<Rightarrow> ('pvar \<Rightarrow> 'pval)) \<Rightarrow> 'lval))" (* |lval| \<ge> |PStates^k| *)
      and "c \<noteq> x"
      and "injective from_nat"
      and "not_free_var_of (P :: ('a \<Rightarrow> ('lvar \<Rightarrow> 'lval) \<times> ('pvar \<Rightarrow> 'pval)) set) x \<and> not_free_var_of P c"
      and "not_free_var_of Q x \<and> not_free_var_of Q c"
    shows "RIL P C Q \<longleftrightarrow> \<Turnstile> {pre_insec from_nat x c P} C {post_insec from_nat x c Q}"
  using assms(1) assms(2) assms(3) assms(4) assms(5) assms(6) by (rule encoding_RIL)

theorem encoding_FU_in_HHL:
  "FU P C Q \<longleftrightarrow> \<Turnstile> {encode_FU P} C {encode_FU Q}"
  by (rule encoding_FU)

theorem FU_hyperproperties:
  "hypersat C (hyperprop_FU P Q) \<longleftrightarrow> FU P C Q"
  by (rule FU_expresses_hyperproperties)

text \<open>RFU is the old name of k-FU\<close>

theorem encode_RFU_in_HHL:
  assumes "not_free_var_of P x"
      and "not_free_var_of Q x"
      and "injective from_nat"
    shows "RFU P C Q \<longleftrightarrow> \<Turnstile> {encode_RFU from_nat x P} C {encode_RFU from_nat x Q}"
  using assms
  by (rule encode_RFU)


theorem RFU_expresses_hyperproperties:
  "hypersat C (RFU_hyperprop P Q) \<longleftrightarrow> RFU P C Q"
  by (rule RFU_captures_hyperproperties)



text \<open>RUE is the old name of k-UE\<close>

theorem RUE_expresses_hyperproperty:
  "RUE P C Q \<longleftrightarrow> hypersat C (hyperprop_RUE P Q)"
  by (rule RUE_express_hyperproperties)


theorem encoding_RUE_in_HHL:
  assumes "injective fn \<and> injective fn1 \<and> injective fn2"
      and "t \<noteq> x"
      and "injective (fn :: nat \<Rightarrow> 'a)"
      and "injective fn1"
      and "injective fn2"
      and "not_in_free_vars_double {x, t} P"
      and "not_in_free_vars_double {x, t} Q"

  shows "RUE P C Q \<longleftrightarrow> \<Turnstile> {encode_RUE_1 fn fn1 fn2 x t P} C {encode_RUE_2 fn fn1 fn2 x t Q}"
  using assms by (rule encoding_RUE)




text \<open>Example 4\<close>
theorem proving_refinement:
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








subsection \<open>Appendix D: Compositionality\<close>

subsubsection \<open>Rules from D.1\<close>

proposition Linking:
  assumes "\<And>\<phi>1 (\<phi>2 :: ('a, 'b, 'c, 'd) state). fst \<phi>1 = fst \<phi>2 \<and> ( \<Turnstile> { (in_set \<phi>1 :: (('a, 'b, 'c, 'd) state) hyperassertion) } C { in_set \<phi>2 } )
  \<Longrightarrow> ( \<Turnstile> { (P \<phi>1 :: (('a, 'b, 'c, 'd) state) hyperassertion) } C { Q \<phi>2 } )"
  shows "\<Turnstile> { ((\<lambda>S. \<forall>\<phi>1 \<in> S. P \<phi>1 S) :: (('a, 'b, 'c, 'd) state) hyperassertion) } C { (\<lambda>S. \<forall>\<phi>2 \<in> S. Q \<phi>2 S) }"
  using assms by (rule rule_linking)

proposition And_rule:
  assumes "\<Turnstile> {P} C {Q}"
      and "hyper_hoare_triple P' C Q'"
    shows "hyper_hoare_triple (conj P P') C (conj Q Q')"
  using assms by (rule rule_And)

proposition Or_rule:
  assumes "\<Turnstile> {P} C {Q}"
      and "\<Turnstile> {P'} C {Q'}"
    shows "hyper_hoare_triple (disj P P') C (disj Q Q')"
  using assms by (rule rule_Or)

proposition FrameSafe:
  assumes "wr C \<inter> fv F = {}"
      and "wf_assertion F"
      and "no_exists_state F"
    shows "\<Turnstile> {interp_assert F} C {interp_assert F}"
  using safe_frame_rule_syntactic assms by auto

proposition Forall_rule:
  assumes "\<And>x. \<Turnstile> {P x} C {Q x}"
  shows "hyper_hoare_triple (forall P) C (forall Q)"
  using assms by (rule rule_Forall)

proposition rule_IndexedUnion:
  assumes "\<And>x. \<Turnstile> {P x} C {Q x}"
  shows "hyper_hoare_triple (general_join P) C (general_join Q)"
  using assms by (rule rule_IndexedUnion)

proposition rule_Union:
  assumes "\<Turnstile> {P} C {Q}"
      and "hyper_hoare_triple P' C Q'"
    shows "hyper_hoare_triple (join P P') C (join Q Q')"
  using assms by (rule rule_Union)

proposition rule_BigUnion:
  fixes P :: "((('a \<Rightarrow> 'b) \<times> ('c \<Rightarrow> 'd)) set \<Rightarrow> bool)"
  assumes "\<Turnstile> {P} C {Q}"
  shows "\<Turnstile> {general_union P} C {general_union Q}"
  using assms by (rule rule_BigUnion)

proposition Specialize:
  assumes "\<Turnstile> {interp_assert P} C {interp_assert Q}"
      and "indep_of_set b"
      and "wf_assertion_aux 0 1 b"
      and "wr C \<inter> fv b = {}"
    shows "\<Turnstile> { interp_assert (transform_assume b P) } C { interp_assert (transform_assume b Q) }"
  using filter_rule_syntactic assms by blast

proposition LUpdate:
  assumes "\<Turnstile> {P'} C {Q}"
      and "entails_with_updates vars P P'"
      and "invariant_on_updates vars Q"
    shows "\<Turnstile> {P} C {Q}"
  using assms by (rule rule_LUpdate)

proposition LUpdateSyntactic:
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
  "hyper_hoare_triple P C (\<lambda>_. True)"
  by (rule rule_True)

proposition rule_False:
  "hyper_hoare_triple (\<lambda>_. False) C Q"
  by (rule rule_False)

proposition rule_Empty:
  "\<Turnstile> { (\<lambda>S. S = {}) } C { (\<lambda>S. S = {}) }"
  by (rule rule_Empty)




subsubsection \<open>Examples from D.2\<close>


proposition composing_monotonicity_and_minimum:
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




proposition composing_GNI_with_SNI:
  fixes h :: 'lvar
  fixes l :: 'pvar
  assumes "\<Turnstile> { (low l :: (('lvar, 'lval, 'pvar, 'pval) state) hyperassertion) } C2 { low l }"
      and "\<Turnstile> { (not_empty :: (('lvar, 'lval, 'pvar, 'pval) state) hyperassertion) } C2 { not_empty }"
      and "\<Turnstile> { (low l :: (('lvar, 'lval, 'pvar, 'pval) state) hyperassertion) } C1 { lGNI l h }"
    shows "\<Turnstile> { (low l :: (('lvar, 'lval, 'pvar, 'pval) state) hyperassertion) } C1;; C2 { lGNI l h }"
  using assms by (rule composing_GNI_with_SNI)







subsection \<open>Appendix E: Termination-Based Reasoning\<close>



theorem while_synchronized_total:
  assumes "wfP lt"
      and "\<And>n. not_fv_hyper t (I n)"
      and "\<And>n. \<Turnstile>TOT {conj (conj (I n) (holds_forall b)) (e_recorded_in_t e t)} C {conj (conj (I (Suc n)) (low_exp b)) (e_smaller_than_t e t lt)}"
    shows "\<Turnstile>TOT {conj (I 0) (low_exp b)} while_cond b C {conj (exists I) (holds_forall (lnot b))}"
  using assms while_synchronized_tot by meson

theorem frame_rule:
  assumes "\<Turnstile>TOT {P} C {Q}"
      and "wr C \<inter> fv F = {}"
      and "wf_assertion F"
    shows "\<Turnstile>TOT {conj P (interp_assert F)} C {conj Q (interp_assert F)}"
  by (simp add: assms(1) assms(2) assms(3) frame_rule_syntactic)




subsection \<open>Appendix I: Synchronous Reasoning over Different Branches\<close>

theorem synchronized_if_rule:
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