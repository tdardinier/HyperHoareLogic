theory AutomatingHHL
  imports PaperResults
begin

text \<open>This file contains the formal results mentioned the paper:
\<^item> Theorem 1 from section 4.2: see theorem \<open>while_general_auto\<close> at the end of the file.
\<^item> Lemma 1 from section 4.3: see lemma \<open>sound_framing_over\<close> at the end of the file.\<close>

text \<open>Navigating the Isabelle formalization:
\<^item> You can use the panel "Sidekick" on the right to see and navigate the structure of the file, via sections and subsections.
\<^item> You can ctrl+click on terms to jump to their definition.
\<^item> After jumping to another location, you can come back to the previous location by clicking the
  green left arrow, on the right side of the menu above.\<close>

text \<open>Quantified variables and quantified states are represented as de Bruijn indices (natural numbers).
We use a list of values and a list of states to track quantified values and states, respectively.\<close>

fun sp_assume :: "('a nstate \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> 'a nstate list \<Rightarrow> 'a assertion \<Rightarrow> 'a nstate hyperassertion" 
  where
  "sp_assume b vals states (AForallState A) S \<longleftrightarrow> (\<forall>\<phi>\<in>S. sp_assume b vals (\<phi> # states) A S)"
| "sp_assume b vals states (AExistsState A) S \<longleftrightarrow> (\<exists>\<phi>. sp_assume b vals (\<phi> # states) A S \<and> (b \<phi> \<longrightarrow> \<phi> \<in> S))"
| "sp_assume b vals states (AForall A) S \<longleftrightarrow> (\<forall>v. sp_assume b (v # vals) states A S)"
| "sp_assume b vals states (AExists A) S \<longleftrightarrow> (\<exists>v. sp_assume b (v # vals) states A S)"
| "sp_assume b vals states (AAnd A B) S \<longleftrightarrow> sp_assume b vals states A S \<and> sp_assume b vals states B S"
| "sp_assume b vals states (AOr A B) S \<longleftrightarrow> sp_assume b vals states A S \<or> sp_assume b vals states B S"
| "sp_assume b vals states A S \<longleftrightarrow> sat_assertion vals states A S" (* AConst and AComp *)

lemma sp_assume_works:
  assumes "sat_assertion vals states A S"
  shows "sp_assume b vals states A (Set.filter b S)"
  using assms
  by (induct A arbitrary: vals states) (auto)

lemma up_closed_from_no_forall_state_sp_assume:
  assumes "no_forall_state A"
      and "sp_assume b vals states A (S n)"
    shows "sp_assume b vals states A (\<Union>n. S n)"
  using assms
by (induct A arbitrary: vals states) auto

lemma sp_assume_upwards_closed_aux:
  assumes "no_forall_state_after_existential A"
      and "ascending S"
      and "\<And>n. sp_assume b vals states A (S n)"
    shows "sp_assume b vals states A (\<Union>(n::nat). S n)"
  using assms
proof (induct A arbitrary: vals states S)
  case (AForallState A)
  have "\<And>\<phi>. \<phi> \<in> (\<Union> (range S)) \<Longrightarrow> sp_assume b vals (\<phi> # states) A (\<Union> (range S))"
  proof -
    fix \<phi> assume asm0: "\<phi> \<in> (\<Union> (range S))"
    then obtain n where "\<phi> \<in> S n" by blast
    then have "\<And>m. m \<ge> n \<Longrightarrow> sp_assume b vals (\<phi> # states) A (S m)"
      by (metis AForallState.prems(2) AForallState.prems(3) ascending_def sp_assume.simps(1) subset_eq)

    let ?S = "shift_sequence S n"

    have "sp_assume b vals (\<phi> # states) A (\<Union> (range ?S))"
    proof (rule AForallState(1))
      show "no_forall_state_after_existential A"
        using AForallState.prems(1) by auto
      show "ascending ?S"
        by (simp add: AForallState.prems(2) shift_sequence_properties(1))
      fix m show "sp_assume b vals (\<phi> # states) A (shift_sequence S n m)"
        by (simp add: \<open>\<And>m. n \<le> m \<Longrightarrow> sp_assume b vals (\<phi> # states) A (S m)\<close> shift_sequence_def)
    qed
    then show "sp_assume b vals (\<phi> # states) A (\<Union> (range S))"
      using AForallState.prems(2) shift_sequence_properties(2) by fastforce
  qed
  then show "sp_assume b vals states (AForallState A) (\<Union> (range S))"
    by simp
next
  case (AExistsState A)
  then show ?case
    by (meson no_forall_state.simps(4) no_forall_state_after_existential.simps(8) up_closed_from_no_forall_state_sp_assume)
next
  case (AExists A)
  then show ?case
    by (meson no_forall_state.simps(6) no_forall_state_after_existential.simps(7) up_closed_from_no_forall_state_sp_assume)
next
  case (AOr A1 A2) \<comment> \<open>either A1 is infinitely often true, or either A2 is...\<close>
  show ?case
  proof (cases "holds_infinitely_often (sp_assume b vals states A1) S")
    case True
    then have "sp_assume b vals states A1 (\<Union> (range (subseq_sat (sp_assume b vals states A1) S)))"
      using AOr.hyps(1) AOr.prems(1) AOr.prems(2) subseq_sat_properties(1) subseq_sat_properties(2) no_forall_state_after_existential.simps(6) by blast
    then show ?thesis
      using AOr.prems(2) True subseq_sat_properties(3) by fastforce
  next
    case False
    then obtain n where "\<And>m. m > n \<Longrightarrow> \<not> sp_assume b vals states A1 (S m)"
      using holds_infinitely_often_def[of "sp_assume b vals states A1" S] by blast
    then have "\<And>m. m > n \<Longrightarrow> sp_assume b vals states A2 (S m)"
      using AOr.prems(3) by auto
    then have "holds_infinitely_often (sp_assume b vals states A2) S"
      using holds_infinitely_often_def[of "sp_assume b vals states A2" S]
      by (metis less_Suc_eq nat_neq_iff)
    then have "sp_assume b vals states A2 (\<Union> (range (subseq_sat (sp_assume b vals states A2) S)))"
      using AOr.hyps(2) AOr.prems(1) AOr.prems(2) subseq_sat_properties(1) subseq_sat_properties(2) no_forall_state_after_existential.simps(6) by blast
    then show ?thesis
      by (metis AOr.prems(2) \<open>holds_infinitely_often (sp_assume b vals states A2) S\<close> sp_assume.simps(6) subseq_sat_properties(3))
  qed
qed (auto)


definition upwards_closed_no_index where
  "upwards_closed_no_index P \<longleftrightarrow> (\<forall>S. ascending S \<and> (\<forall>n. P (S n)) \<longrightarrow> P (\<Union>n. S n))"

lemma upwards_closed_no_indexI:
  assumes "\<And>S. ascending S \<Longrightarrow> (\<forall>n. P (S n)) \<Longrightarrow> P (\<Union>n. S n)"
  shows "upwards_closed_no_index P"
  by (simp add: assms upwards_closed_no_index_def)

lemma sp_assume_upwards_closed:
  assumes "no_forall_state_after_existential A"
    shows "upwards_closed_no_index (sp_assume b vals states A)"
proof (rule upwards_closed_no_indexI)
  fix S assume "ascending S" "\<forall>(n::nat). sp_assume b vals states A (S n)"
  then show "sp_assume b vals states A (\<Union> (range S))" using sp_assume_upwards_closed_aux[of A S b vals states]
    using assms by blast
qed


lemma upwards_closed_no_index_conj:
  assumes "upwards_closed_no_index A"
      and "upwards_closed_no_index B"
    shows "upwards_closed_no_index (conj A B)"
  by (metis assms(1) assms(2) conj_def upwards_closed_no_index_def)

lemma upwards_closed_forall:
  "upwards_closed_no_index (\<lambda>S. \<forall>\<phi>\<in>S. P \<phi>)"
  by (simp add: upwards_closed_no_index_def)

theorem while_general_no_index:
  assumes "\<Turnstile> {P} if_then b C {P}"
      and "\<Turnstile> {P} Assume (lnot b) {Q}"
      and "upwards_closed_no_index Q"
    shows "\<Turnstile> {P} while_cond b C {Q}"
proof (rule hyper_hoare_tripleI)
  fix S assume asm0: "P S"
  then have "\<And>n. P (iterate_sem n (if_then b C) S)"
    by (meson assms(1) indexed_invariant_then_power)
  then have "\<And>n. Q  (filter_exp (lnot b) (union_up_to_n (if_then b C) S n))"
    by (metis assms(2) assume_sem filter_exp_def hyper_hoare_triple_def iterate_sem_assume_increasing_union_up_to)
  moreover have "ascending (\<lambda>n. filter_exp (lnot b) (union_up_to_n (if_then b C) S n))"
    by (simp add: ascending_iterate_filter)
  ultimately have "Q (sem (while_cond b C) S)"
    by (metis (no_types, lifting) SUP_cong assms(3) filter_exp_union_general iterate_sem_assume_increasing_union_up_to sem_while_with_if upwards_closed_no_index_def)
  then show "Q (sem (while_cond b C) S)"
    by (simp add: conj_def filter_exp_def holds_forall_def sem_while_with_if)
qed


lemma while_exists_frame:
  assumes "\<And>\<phi>. \<Turnstile> { conj (P \<phi>) F } while_cond b C { Q \<phi> }"
  shows "\<Turnstile> { (\<lambda>S. (\<exists>\<phi> \<in> S. \<not> b (snd \<phi>) \<and> P \<phi> S) \<and> F S) } while_cond b C { (\<lambda>S. \<exists>\<phi> \<in> S. Q \<phi> S) }"
proof (rule hyper_hoare_tripleI)
  fix S assume "(\<exists>\<phi>\<in>S. \<not> b (snd \<phi>) \<and> P \<phi> S) \<and> F S"
  then obtain \<phi> where asm0: "\<phi>\<in>S" "\<not> b (snd \<phi>) \<and> P \<phi> S" by blast
  then have "Q \<phi> (sem (while_cond b C) S)"
    by (metis \<open>(\<exists>\<phi>\<in>S. \<not> b (snd \<phi>) \<and> P \<phi> S) \<and> F S\<close> assms conj_def hyper_hoare_triple_def)
  then show "\<exists>\<phi>\<in>sem (while_cond b C) S. Q \<phi> (sem (while_cond b C) S)"
    using asm0(1) asm0(2) false_state_in_while_cond by blast
qed



lemma exists_terminates_loop:
  assumes "wfP lt"
      and "\<And>v. \<Turnstile> { (\<lambda>S. (\<exists>\<phi>\<in>S. e (snd \<phi>) = v \<and> b (snd \<phi>) \<and> P \<phi> S) \<and> F S) } if_then b C { (\<lambda>S. (\<exists>\<phi>\<in>S. lt (e (snd \<phi>)) v \<and> P \<phi> S) \<and> F S) }"
      and "\<And>\<phi>. \<Turnstile> { conj (P \<phi>) F } while_cond b C { Q \<phi> }"
    shows "\<Turnstile> { (\<lambda>S. (\<exists>\<phi>\<in>S. P \<phi> S) \<and> F S) } while_cond b C { (\<lambda>S. \<exists>\<phi>\<in>S. Q \<phi> S) }"
proof (rule hyper_hoare_tripleI)
  fix S assume asm0: "(\<exists>\<phi>\<in>S. P \<phi> S) \<and> F S"
  then obtain \<phi> where "\<phi> \<in> S" "P \<phi> S" by blast
  show "\<exists>\<phi>\<in>sem (while_cond b C) S. Q \<phi> (sem (while_cond b C) S)"
  proof (cases "b (snd \<phi>)")
    case True

    let ?R = "{(x, y). lt x y}"
    let ?Q = "{ e (snd \<phi>') |\<phi>' n. \<phi>' \<in> iterate_sem n (if_then b C) S \<and> b (snd \<phi>') \<and> P \<phi>' (iterate_sem n (if_then b C) S) \<and> F (iterate_sem n (if_then b C) S) }"
  
    have main_res: "\<exists>n \<phi>'. \<phi>' \<in> iterate_sem n (if_then b C) S \<and> \<not> b (snd \<phi>') \<and> P \<phi>' (iterate_sem n (if_then b C) S) \<and> F (iterate_sem n (if_then b C) S)"
    proof (rule wfE_min)
      show "wf ?R"
        using assms(1) wfP_def by blast
      show "e (snd \<phi>) \<in> ?Q"
        using True \<open>P \<phi> S\<close> \<open>\<phi> \<in> S\<close> iterate_sem.simps(1)
        by (smt (verit, best) asm0 mem_Collect_eq)
      fix z
      assume asm1: "z \<in> ?Q" "\<And>y. (y, z) \<in> ?R \<Longrightarrow> y \<notin> ?Q"
      then obtain n \<phi>' where "\<phi>' \<in> iterate_sem n (if_then b C) S" "b (snd \<phi>')" "P \<phi>' (iterate_sem n (if_then b C) S)" "z = e (snd \<phi>')" "F (iterate_sem n (if_then b C) S)"
        by blast
      then have "(\<lambda>S. (\<exists>\<phi>\<in>S. (b (snd \<phi>) \<longrightarrow> lt (e (snd \<phi>)) z) \<and> P \<phi> S) \<and> F S) (sem (if_then b C) ((iterate_sem n (if_then b C) S)))"
        using assms(2) hyper_hoare_tripleE by blast
      then obtain \<phi>'' where "(b (snd \<phi>'') \<longrightarrow> lt (e (snd \<phi>'')) z) \<and> P \<phi>'' (sem (if_then b C) ((iterate_sem n (if_then b C) S)))"
        "\<phi>'' \<in> (sem (if_then b C) ((iterate_sem n (if_then b C) S)))"
        by blast
      then have "\<not> b (snd \<phi>'')"
        by (metis (mono_tags, lifting) \<open>(\<exists>\<phi>\<in>sem (if_then b C) (iterate_sem n (if_then b C) S). (b (snd \<phi>) \<longrightarrow> lt (e (snd \<phi>)) z) \<and> P \<phi> (sem (if_then b C) (iterate_sem n (if_then b C) S))) \<and> F (sem (if_then b C) (iterate_sem n (if_then b C) S))\<close> asm1(2) case_prodI iterate_sem.simps(2) mem_Collect_eq)
      then show "\<exists>n \<phi>'. \<phi>' \<in> iterate_sem n (if_then b C) S \<and> \<not> b (snd \<phi>') \<and> P \<phi>' (iterate_sem n (if_then b C) S) \<and> F (iterate_sem n (if_then b C) S)"
        by (metis \<open>(\<exists>\<phi>\<in>sem (if_then b C) (iterate_sem n (if_then b C) S). (b (snd \<phi>) \<longrightarrow> lt (e (snd \<phi>)) z) \<and> P \<phi> (sem (if_then b C) (iterate_sem n (if_then b C) S))) \<and> F (sem (if_then b C) (iterate_sem n (if_then b C) S))\<close> \<open>(b (snd \<phi>'') \<longrightarrow> lt (e (snd \<phi>'')) z) \<and> P \<phi>'' (sem (if_then b C) (iterate_sem n (if_then b C) S))\<close> \<open>\<phi>'' \<in> sem (if_then b C) (iterate_sem n (if_then b C) S)\<close> iterate_sem.simps(2))
    qed
    then obtain n \<phi>' where "\<phi>' \<in> iterate_sem n (if_then b C) S" "\<not> b (snd \<phi>')" "P \<phi>' (iterate_sem n (if_then b C) S)" "F (iterate_sem n (if_then b C) S)"
      by blast
    then have "\<exists>\<phi>\<in>sem (while_cond b C) (iterate_sem n (if_then b C) S). Q \<phi> (sem (while_cond b C) (iterate_sem n (if_then b C) S)) \<and> F (iterate_sem n (if_then b C) S)"
      using while_exists_frame[of P F b C Q] assms(3) hyper_hoare_tripleE[of "(\<lambda>S. (\<exists>\<phi>\<in>S. \<not> b (snd \<phi>) \<and> P \<phi> S) \<and> F S)" "while_cond b C" "\<lambda>S. (\<exists>\<phi>\<in>S. Q \<phi> S)"]
      by blast
    then show "(\<exists>\<phi>\<in>sem (while_cond b C) S. Q \<phi> (sem (while_cond b C) S))"
      by (metis unroll_while_sem)
  next
    case False
    then show ?thesis
      using while_exists_frame[of P F b C Q] assms(3) hyper_hoare_tripleE \<open>P \<phi> S\<close> \<open>\<phi> \<in> S\<close>
      using asm0 by blast
  qed
qed

corollary exists_terminates_loop_auto:
  assumes "wfP lt"
      and "\<And>v. \<Turnstile> { (\<lambda>S. (\<exists>\<phi>\<in>S. e (snd \<phi>) = v \<and> b (snd \<phi>) \<and> P \<phi> S) \<and> F S) } if_then b C { (\<lambda>S. (\<exists>\<phi>\<in>S. lt (e (snd \<phi>)) v \<and> P \<phi> S) \<and> F S) }"
      and "\<And>\<phi>. \<Turnstile> { conj (P \<phi>) F } while_cond b C { conj (P \<phi>) F }"
    shows "\<Turnstile> { (\<lambda>S. (\<exists>\<phi>\<in>S. P \<phi> S) \<and> F S) } while_cond b C { (\<lambda>S. (\<exists>\<phi>\<in>S. P \<phi> S) \<and> F S) }"
proof (rule consequence_rule)
  show "\<Turnstile> {(\<lambda>S. (\<exists>\<phi>\<in>S. P \<phi> S) \<and> F S)} while_cond b C {\<lambda>S. \<exists>\<phi>\<in>S. Logic.conj (P \<phi>) F S}"
    using exists_terminates_loop[of lt e b P F C "\<lambda>\<phi>. conj (P \<phi>) F"]
    using assms(1) assms(2) assms(3) by fastforce
  show "entails (\<lambda>S. \<exists>\<phi>\<in>S. Logic.conj (P \<phi>) F S) (\<lambda>S. (\<exists>\<phi>\<in>S. P \<phi> S) \<and> F S)"
    by (simp add: conj_def entails_def)
qed (simp add: entails_refl)


section \<open>Results from the Hypra paper\<close>

text \<open>Theorem 1: Novel loop rule for \<open>\<forall>*\<exists>*\<close>-hyperproperties\<close>

text \<open>This result uses the following constructs:
\<^item> \<^term>\<open>conj A B\<close> corresponds to the hyper-assertion \<open>A \<and> B\<close>.
\<^item> \<^term>\<open>sp_assume (lnot b \<circ> snd) [] [] I\<close> corresponds to \<open>\<Theta>\<^sub>\<not>\<^sub>b(I)\<close>.
\<^item> \<^term>\<open>holds_forall b\<close> corresponds to \<open>box(b)\<close>.\<close>

theorem while_general_auto:
  assumes "\<Turnstile> {interp_assert I} if_then b C {interp_assert I}"
      and "no_forall_state_after_existential I"
    shows "\<Turnstile> {interp_assert I} while_cond b C { conj (sp_assume (lnot b \<circ> snd) [] [] I) (holds_forall (lnot b)) }"
  using assms(1)
proof (rule while_general_no_index)
  show "upwards_closed_no_index (Logic.conj (sp_assume (lnot b \<circ> snd) [] [] I) (holds_forall (lnot b)))"
  proof (rule upwards_closed_no_index_conj)
    show "upwards_closed_no_index (holds_forall (lnot b))"
      by (metis (no_types, opaque_lifting) holds_forall_def mem_simps(8) upwards_closed_no_indexI)
    show "upwards_closed_no_index (sp_assume (lnot b \<circ> snd) [] [] I)"
      by (simp add: assms(2) sp_assume_upwards_closed)
  qed
  show "\<Turnstile> {interp_assert I} Assume (lnot b) {Logic.conj (sp_assume ((lnot b) \<circ> snd) [] [] I) (holds_forall (lnot b))}"
  proof (rule hyper_hoare_tripleI)
    fix S assume asm0: "interp_assert I S"
    then have "sp_assume (lnot b \<circ> snd) [] [] I (sem (Assume (lnot b)) S)"
      by (simp add: assume_sem sp_assume_works)
    moreover have "holds_forall (lnot b) (sem (Assume (lnot b)) S)"
      by (simp add: assume_sem holds_forall_def)
    ultimately show "Logic.conj (sp_assume (lnot b \<circ> snd) [] [] I) (holds_forall (lnot b)) (sem (Assume (lnot b)) S)"
      by (simp add: conj_def)
  qed
qed

text \<open>Lemma 1.\<close>

text \<open>In the formalization, states have a logical part (omitted in the paper) as well as a program part.
Our lemma below expresses equality of the logical parts (fst), and equality of non-modified variables
for the program part (snd).\<close>

lemma sound_framing_over:
  "\<forall>\<sigma>' \<in> sem C S. \<exists>\<sigma> \<in> S. (\<forall>x. x \<notin> wr C \<longrightarrow> snd \<sigma> x = snd \<sigma>' x) \<and> fst \<sigma> = fst \<sigma>'"
proof clarify
  fix l \<sigma>' assume asm0: "(l, \<sigma>') \<in> sem C S"
  then obtain \<sigma> where "(l, \<sigma>) \<in> S" "\<langle>C, \<sigma>\<rangle> \<rightarrow> \<sigma>'"
    by (metis in_sem prod.sel(1) prod.sel(2))
  then have "agree_on (- wr C) \<sigma> \<sigma>'"
    by (simp add: wr_charact)
  then show "\<exists>\<sigma>\<in>S. (\<forall>x. x \<notin> wr C \<longrightarrow> snd \<sigma> x = snd (l, \<sigma>') x) \<and> fst \<sigma> = fst (l, \<sigma>')"
    by (metis (mono_tags, lifting) ComplI \<open>(l, \<sigma>) \<in> S\<close> agree_onE fst_conv snd_conv)
qed


end