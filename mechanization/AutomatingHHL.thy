theory AutomatingHHL
  imports PaperResults
begin

(* transforms the syntactic assertion into a semantic one, because we don't have <\<sigma>> *)
fun sp_assume where
  "sp_assume b vals states (AForallState A) S \<longleftrightarrow> (\<forall>\<phi>\<in>S. sp_assume b vals (\<phi> # states) A S)"
(*
  "sp_assume b vals states (AForallState A) S \<longleftrightarrow> (\<forall>\<phi>\<in>S. b \<phi> \<and> sp_assume b vals (\<phi> # states) A S)"
*)
| "sp_assume b vals states (AExistsState A) S \<longleftrightarrow> (\<exists>\<phi>. sp_assume b vals (\<phi> # states) A S \<and> (b \<phi> \<longrightarrow> \<phi> \<in> S))"
| "sp_assume b vals states (AForall A) S \<longleftrightarrow> (\<forall>v. sp_assume b (v # vals) states A S)"
| "sp_assume b vals states (AExists A) S \<longleftrightarrow> (\<exists>v. sp_assume b (v # vals) states A S)"
| "sp_assume b vals states (AAnd A B) S \<longleftrightarrow> sp_assume b vals states A S \<and> sp_assume b vals states B S"
| "sp_assume b vals states (AOr A B) S \<longleftrightarrow> sp_assume b vals states A S \<or> sp_assume b vals states B S"
| "sp_assume b vals states A S \<longleftrightarrow> sat_assertion vals states A S" (* AConst and AComp *)

lemma sp_assume_works:
  assumes "sat_assertion vals states A S"
  shows "sp_assume b vals states A (Set.filter b S)" (* Set.filter (bsem \<circ> snd) S *)
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
(*
    moreover have "b \<phi>"
      using AForallState.prems(3) \<open>\<phi> \<in> S n\<close> by auto
*)
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
  case (AOr A1 A2)
(* either A1 is infinitely often true, or either A2 is... *)
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
    shows "\<Turnstile> {P} while_cond b C {Q}" (* should we add back the *\<forall><\<sigma>>. \<not> b(\<sigma>) *)
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


(* TODO:
Prove the rule with the transformation
*)

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

(* TODO: prove that's is the strongest post? *)







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









































definition after_assume where
  "after_assume I b S' = (\<exists>S. S' = sem (Assume (lnot b)) S \<and> I S)"

lemma after_assume_same:
  assumes "sat_assertion vals states A S"
  shows "sp_assume (b \<circ> snd) vals states A (sem (Assume b) S)"
  using sp_assume_works[of vals states A S] assms assume_sem[of b S] by simp

(* is A stable by union? 
No if there is \<forall>\<forall>
low(l)
*)

definition limit_set where
  "limit_set S = { \<sigma> |\<sigma> n. \<forall>m \<ge> n. \<sigma> \<in> S m}"

lemma limit_setE:
  "\<sigma> \<in> limit_set S \<Longrightarrow> (\<exists>n. \<forall>m \<ge> n. \<sigma> \<in> S m)"
  by (simp add: limit_set_def)

lemma limit_setI:
  assumes "\<And>m. m \<ge> n \<Longrightarrow> \<sigma> \<in> S m"
  shows "\<sigma> \<in> limit_set S"
  using assms limit_set_def by force

lemma equality_of_sets:
  assumes "ascending (Set.filter b \<circ> S)"
  shows "(\<Union>n. Set.filter b (S n)) = Set.filter b (limit_set S)" (is "?A = ?B")
proof
  show "?A \<subseteq> ?B"
  proof
    fix \<sigma> assume "\<sigma> \<in> ?A"
    then obtain n where "\<sigma> \<in> S n" "b \<sigma>"
      by force
    moreover have "\<sigma> \<in> limit_set S"
    proof (rule limit_setI)
      fix m show "n \<le> m \<Longrightarrow> \<sigma> \<in> S m"
        by (metis (no_types, lifting) ascending_def assms calculation(1) calculation(2) comp_apply member_filter subset_eq)
    qed
    ultimately show "\<sigma> \<in> ?B"
      by auto
  qed
  show "?B \<subseteq> ?A"
  proof
    fix \<sigma> assume "\<sigma> \<in> ?B"
    then obtain n where "b \<sigma>" "\<And>m. m \<ge> n \<Longrightarrow> \<sigma> \<in> S m"   
      by (metis limit_setE member_filter)
    then show "\<sigma> \<in> ?A"
      by auto
  qed
qed

lemma while_sem_new_limit:
  "sem (while_cond b C) S = Set.filter (lnot b \<circ> snd) (limit_set (\<lambda>n. iterate_sem n (if_then b C) S))"
proof -
  have "filter_exp (lnot b) (\<Union>n. iterate_sem n (if_then b C) S) = Set.filter (lnot b \<circ> snd) (limit_set (\<lambda>n. iterate_sem n (if_then b C) S))"
    using equality_of_sets
    by (smt (verit, best) Sup.SUP_cong ascendingI comp_apply filter_exp_def filter_exp_union_general iterate_sem_assume_increasing)
  then show ?thesis using sem_while_with_if by blast
qed

(* might not work for disjunctions... *)

lemma new_powerful_lemma:
  assumes "no_forall_state_after_existential A"
      and "\<And>n. sat_assertion vals states A (S n)"
    shows "sat_assertion vals states A (limit_set S)"
  using assms
proof (induct A arbitrary: vals states S)
  case (AForallState A)
(*
    no_forall_state_after_existential A \<Longrightarrow> (\<And>n. sat_assertion ?vals ?states A (?S n)) \<Longrightarrow> sat_assertion ?vals ?states A (limit_set ?S)
    no_forall_state_after_existential (AForallState A)
    sat_assertion vals states (AForallState A) (S ?n)
*)
  then have "\<And>n \<phi>. \<phi> \<in> S n \<Longrightarrow> sat_assertion vals (\<phi> # states) A (S n)"
    using sat_assertion.simps(3) by blast
(*
We need to shift, but maybe too much (infinitely...)
*)

  then show "sat_assertion vals states (AForallState A) (limit_set S)" sorry
next
  case (AExistsState A)
(* we can shift by n *)
  then show ?case sorry
next
  case (AForall A)
  then show ?case sorry
next
  case (AExists A)
(* we can shift by n *)
  then show ?case sorry
next
  case (AOr A1 A2)
(*
At least one holds infinitely often...
\<longrightarrow> Is the limit the same if we project? Maybe not...
*)
  then show ?case sorry
qed (auto)


lemma after_assume_same_two:
  assumes "sp_assume (b \<circ> snd) vals states A S'"
      and "\<forall>\<phi> \<in> S'. b (snd \<phi>)"
(*
And A is satisfiable... by something larger than S'?
*)
(* Assume A = A1 \<and> A2 *)
(*
A1 = \<forall><\<phi>>. \<phi>(x) = 5
A2 = \<forall><\<phi>>. \<phi>(x) = 6
S' would not satisfy it...
S' would be empty

*)

(*
How do I construct S?
*)
    shows "\<exists>S. S' = sem (Assume b) S \<and> sat_assertion vals states A S"
  using assms
proof (induct A arbitrary: vals states)
  case (AConst x)
  then show ?case
    by (metis holds_forall_def sem_assume_low_exp(1) sp_assume.simps(7))
next
  case (AComp x1a x2 x3a)
  then show ?case
    by (metis holds_forallI sem_assume_low_exp(1) sp_assume.simps(8))
next
  case (AForallState A)
  then show ?case sorry
next
  case (AExistsState A)
(*
    sp_assume (b \<circ> snd) ?vals ?states A S' \<Longrightarrow> \<forall>\<phi>\<in>S'. b (snd \<phi>) \<Longrightarrow> \<exists>S. S' = sem (Assume b) S \<and> sat_assertion ?vals ?states A S
    sp_assume (b \<circ> snd) vals states (AExistsState A) S'
    \<forall>\<phi>\<in>S'. b (snd \<phi>)
*)
  then obtain \<phi> where "sp_assume (b \<circ> snd) vals (\<phi> # states) A S'" "(b \<circ> snd) \<phi> \<Longrightarrow> \<phi> \<in> S'"
    by (metis sp_assume.simps(2))



  then show "\<exists>S. S' = sem (Assume b) S \<and> sat_assertion vals states (AExistsState A) S" sorry
next
  case (AForall A)
  then show ?case sorry
next
  case (AAnd A1 A2)
(*
  then obtain S1 S2 where "S' = sem (Assume b) S1 \<and> sat_assertion vals states A1 S1"
    "S' = sem (Assume b) S2 \<and> sat_assertion vals states A2 S2"
    by (meson sp_assume.simps(5))

*)


  then show ?case sorry
qed (fastforce+)






lemma upwards_closed_before_then_after:
  assumes "no_forall_state_after_existential I"
  shows "upwards_closed (\<lambda>n. sp_assume b vals states I) (sp_assume b vals states I)"
  by (simp add: assms sp_assume_upwards_closed upwards_closed_def)



lemma no_forall_state_after_existential_sem_after_assume:
  assumes "no_forall_state_after_existential I"
      and "ascending S_not_b" (* the not_b set always increases *)
      and "\<And>n. S_b (Suc n) = f (S_b n)" (* the b_set is a function of itself only *)
      and "\<And>n. S_b n = Set.filter b (S n) \<and> S_not_b n = Set.filter (lnot b) (S n)" (* partition *)
      and "\<And>n. sat_assertion vals states I (S n)"
(* loop sem: \<Union>n. S_not_b n
How do I express Q?
 *)
    shows "\<exists>S_union. sat_assertion vals states I S_union \<and> (\<Union>n. S_not_b n) = Set.filter (lnot b) S_union"
  using assms
proof (induct I arbitrary: vals states S S_b S_not_b)
  case (AForallState A)
(*
... \<Longrightarrow> \<exists>S_union. sat_assertion ?vals ?states A S_union \<and> \<Union> (range S_not_b) = Set.filter (lnot b) S_union
    no_forall_state_after_existential (AForallState A)
    ascending S_not_b
    S_b (Suc ?n) = f (S_b ?n)
    S_b ?n = Set.filter b (S ?n) \<and> S_not_b ?n = Set.filter (lnot b) (S ?n)
    sat_assertion vals states (AForallState A) (S ?n)
*)
(*
Two cases: \<phi> \<in> S_b, or \<phi> \<in> S_not_b 
*)
  then have "\<And>n \<phi>. \<phi> \<in> S n \<Longrightarrow> sat_assertion vals (\<phi> # states) A (S n)"
    by simp
  thm AForallState(1)[of _ _ _ vals "\<phi> # states"]
(*
\<exists>S_union. sat_assertion vals (\<phi> # states) A S_union \<and> \<Union> (range ?S_not_b) = Set.filter (lnot b) S_union
\<longrightarrow> *one* S_union per state \<phi>
\<longrightarrow> How do we construct the final S_union?
*)


  show "\<exists>S_union. sat_assertion vals states (AForallState A) S_union \<and> \<Union> (range S_not_b) = Set.filter (lnot b) S_union"
    sorry
  proof (rule sat_assertion_aforallstateI)
    fix \<phi>
    assume "\<phi> \<in> \<Union> (range S)"
    then obtain n where "\<phi> \<in> S n" by blast
    then have "\<And>m. m \<ge> n \<Longrightarrow> sat_assertion vals (\<phi> # states) A (S m)"
      by (meson AForallState.prems(2) AForallState.prems(3) ascending_def sat_assertion.simps(3) subsetD)
    let ?S = "shift_sequence S n"
    have "sat_assertion vals (\<phi> # states) A (\<Union> (range ?S))"
    proof (rule AForallState(1))
      show "no_forall_state_after_existential A"
        using AForallState.prems(1) by auto
      show "ascending ?S"
        by (simp add: AForallState.prems(2) shift_sequence_properties(1))
      fix m show "sat_assertion vals (\<phi> # states) A (shift_sequence S n m)"
        by (simp add: \<open>\<And>m. n \<le> m \<Longrightarrow> sat_assertion vals (\<phi> # states) A (S m)\<close> shift_sequence_def)
    qed
    then show "sat_assertion vals (\<phi> # states) A (\<Union> (range S))"
      by (metis AForallState.prems(2) shift_sequence_properties(2))
  qed
next
  case (AExistsState A)
  then show ?case
    by (meson no_forall_state.simps(4) no_forall_state_after_existential.simps(8) up_closed_from_no_exists_state_false)
next
  case (AExists A)
  then show ?case
    by (meson no_forall_state.simps(6) no_forall_state_after_existential.simps(7) up_closed_from_no_exists_state_false)
next
  case (AOr A1 A2)
(* either A1 is infinitely often true, or either A2 is... *)
  show ?case
  proof (cases "holds_infinitely_often (sat_assertion vals states A1) S")
    case True
    then have "sat_assertion vals states A1 (\<Union> (range (subseq_sat (sat_assertion vals states A1) S)))"
      using AOr.hyps(1) AOr.prems(1) AOr.prems(2) subseq_sat_properties(1) subseq_sat_properties(2) no_forall_state_after_existential.simps(6) by blast
    then show ?thesis
      using AOr.prems(2) True subseq_sat_properties(3) by fastforce
  next
    case False
    then have "holds_infinitely_often (sat_assertion vals states A2) S"
      using AOr.prems(3) sat_assertion.simps(8) holds_infinitely_often_def
      by (metis gt_ex max_less_iff_conj)
    then have "sat_assertion vals states A2 (\<Union> (range (subseq_sat (sat_assertion vals states A2) S)))"
      using AOr.hyps(2) AOr.prems(1) AOr.prems(2) subseq_sat_properties(1) subseq_sat_properties(2) no_forall_state_after_existential.simps(6) by blast
    then show ?thesis
      using AOr.prems(2) \<open>holds_infinitely_often (sat_assertion vals states A2) S\<close> subseq_sat_properties(3) by fastforce
  qed
next
  case (AAnd A1 A2)
  then show ?case
    using sat_assertion.simps(7) no_forall_state_after_existential.simps(5) by blast
qed (simp_all)








lemma sem_while_with_if_union_outside:
  "sem (while_cond b C) S = (\<Union>n. filter_exp (lnot b) (iterate_sem n (if_then b C) S))"
  by (simp add: filter_exp_union_general sem_while_with_if)


lemma upwards_closed_before_then_after:
  assumes "upwards_closed (\<lambda>n. I) I"
  shows "upwards_closed (\<lambda>n. after_assume I b) (after_assume I b)"
proof (rule upwards_closedI)
  fix S' assume asm0: "ascending S'" "\<forall>n. after_assume I b (S' n)"
  then have "\<And>n. \<exists>S. S' n = sem (Assume (lnot b)) S \<and> I S"
    by (simp add: after_assume_def)
  moreover obtain S where "ascending S" 


theorem while_general_auto:
  assumes "\<Turnstile> {I} if_then b C {I}"
      and "upwards_closed (\<lambda>(n::nat). I) I"
    shows "\<Turnstile> {I} while_cond b C {after_assume I b}"
proof (rule hyper_hoare_tripleI)
  fix S assume asm0: "I S"
  then have "\<And>n. I (iterate_sem n (if_then b C) S)"
    by (meson assms(1) indexed_invariant_then_power)
  then have "\<And>n. after_assume I b (filter_exp (lnot b) (iterate_sem n (if_then b C) S))"
    by (metis after_assume_def assume_sem filter_exp_def)
  moreover have "ascending (\<lambda>n. filter_exp (lnot b) (iterate_sem n (if_then b C) S))"
    by (meson ascendingI iterate_sem_assume_increasing)



  then have "\<And>n. Q n (filter_exp (lnot b) (union_up_to_n (if_then b C) S n))"
    by (metis assms(2) assume_sem filter_exp_def hyper_hoare_triple_def iterate_sem_assume_increasing_union_up_to)

    by (simp add: ascending_iterate_filter)
  ultimately have "Q_inf (sem (while_cond b C) S)"
    by (metis (no_types, lifting) SUP_cong assms(3) filter_exp_union_general iterate_sem_assume_increasing_union_up_to sem_while_with_if upwards_closed_def)
  then show "Logic.conj Q_inf (holds_forall (lnot b)) (sem (while_cond b C) S)"
    by (simp add: conj_def filter_exp_def holds_forall_def sem_while_with_if)
qed




lemma ascending_union_up_to:
  "ascending (\<lambda>n. union_up_to_n (if_then b C) S n)"
  by (simp add: ascending_def union_up_to_increasing)




fun after_assume_indexed where
  "after_assume_indexed I b 0 S' = (\<exists>S. S' = sem (Assume (lnot b)) S \<and> I S)"
| "after_assume_indexed I b (Suc n) S' = (\<exists>S. S' = sem (Assume (lnot b)) S \<and> I S)"
(* needs to relate this existential to the previous one, included *)



(* weird, because goes backward, not unique... will not be ascending...

Can we create it?
(* S n should become larger *)
*)

  then show "after_assume I b (\<Union> (range S'))" sorry
qed


lemma while_forall_exists_simpler_for_automation:
  assumes "\<Turnstile> {interp_assert I} if_then b C {interp_assert I}"
      and "no_forall_state_after_existential I"
    shows "\<Turnstile> {interp_assert I} while_cond b C {after_assume (interp_assert I) b}"
proof -
  have "\<Turnstile> {interp_assert I} while_cond b C {Logic.conj (after_assume (interp_assert I) b) (holds_forall (lnot b))}"
    using assms(1)
  proof (rule while_general)
(*
 1. \<And>n. \<Turnstile> {interp_assert I} Assume (lnot b) {?Q n}
 2. upwards_closed ?Q (after_assume (interp_assert I) b)
*)
    show "upwards_closed (\<lambda>n. after_assume (interp_assert I) b) (after_assume (interp_assert I) b)"
      by (simp add: assms(2) upwards_closed_before_then_after upwards_closed_syn_sem_practical)
    show "\<Turnstile> {interp_assert I} Assume (lnot b) {after_assume (interp_assert I) b}"
      by (metis after_assume_def hyper_hoare_tripleI)
  qed
  then show ?thesis
    by (simp add: conj_def hyper_hoare_triple_def)
qed

lemma no_forall_state_after_existential_sem:
  assumes "no_forall_state_after_existential A"
      and "ascending S"
      and "\<And>n. sat_assertion vals states A (S n)"
    shows "sat_assertion vals states A (\<Union>n. S n)"
  using assms



end