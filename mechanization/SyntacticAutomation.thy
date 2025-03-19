theory SyntacticAutomation
  imports SyntacticAssertions
begin

type_synonym 'a substitution = "var \<Rightarrow> 'a pexp"
type_synonym 'a path_condition = "'a pbexp"

type_synonym 'a characterizer = "('a path_condition \<times> 'a substitution) list"

definition apply_substitution :: "'a substitution \<Rightarrow> 'a npstate \<Rightarrow> 'a npstate" where
  "apply_substitution subst \<sigma> x = interp_pexp (subst x) \<sigma>"

definition correct_characterizer :: "'a characterizer \<Rightarrow> (var, 'a) stmt \<Rightarrow> bool" where
  "correct_characterizer L C \<longleftrightarrow> (\<forall>\<sigma> \<sigma>'. (\<langle>C, \<sigma>\<rangle> \<rightarrow> \<sigma>') \<longleftrightarrow> (\<exists>(pc, subst) \<in> set L. interp_pbexp pc \<sigma> \<and> \<sigma>' = apply_substitution subst \<sigma>))"

lemma correct_characterizerI:
  assumes "\<And>\<sigma> \<sigma>'. \<langle>C, \<sigma>\<rangle> \<rightarrow> \<sigma>' \<Longrightarrow> \<exists>(pc, subst) \<in> set L. interp_pbexp pc \<sigma> \<and> \<sigma>' = apply_substitution subst \<sigma>"
      and "\<And>\<sigma> \<sigma>' pc subst. (pc, subst) \<in> set L \<Longrightarrow> interp_pbexp pc \<sigma> \<Longrightarrow> \<sigma>' = apply_substitution subst \<sigma> \<Longrightarrow> \<langle>C, \<sigma>\<rangle> \<rightarrow> \<sigma>'"
    shows "correct_characterizer L C"
  by (smt (verit, ccfv_SIG) assms(1) assms(2) case_prodE correct_characterizer_def)

lemma correct_characterizer_sem_charact:
  assumes "correct_characterizer L C"
  shows "sem C S = {(l, apply_substitution subst \<sigma>) |l \<sigma> subst pc. (l, \<sigma>) \<in> S \<and> (pc, subst) \<in> set L \<and> interp_pbexp pc \<sigma>}" (is "?A = ?B")
  unfolding sem_def
  apply rule
  apply rule
  using assms unfolding correct_characterizer_def
  apply simp
   apply blast
  using assms unfolding correct_characterizer_def
  apply simp
  by blast


definition identity_substitution :: "'a substitution" where
  "identity_substitution x = PVar x"

lemma identity_substitution_is_identity:
  "apply_substitution identity_substitution \<sigma> = \<sigma>"
  unfolding apply_substitution_def identity_substitution_def interp_pexp.simps
  by simp


fun transform_exp :: "(nat \<Rightarrow> 'a substitution) \<Rightarrow> 'a exp \<Rightarrow> 'a exp" where
  "transform_exp m (EPVar st y) = pexp_to_exp st (m st y)"
| "transform_exp m (EBinop e1 bop e2) = EBinop (transform_exp m e1) bop (transform_exp m e2)"
| "transform_exp m (EFun f e) = EFun f (transform_exp m e)"
| "transform_exp m e = e"


fun transform_states_aux :: "nat \<Rightarrow> (nat \<Rightarrow> 'a substitution) \<Rightarrow> 'a nstate list \<Rightarrow> 'a nstate list" where
  "transform_states_aux n m [] = []"
| "transform_states_aux n m (\<sigma> # l) = (fst \<sigma>, (\<lambda>x. interp_pexp (m n x) (snd \<sigma>))) # transform_states_aux (Suc n) m l"

abbreviation transform_states where
  "transform_states \<equiv> transform_states_aux 0"

lemma charact_transform_states_snd:
  assumes "st < length states"
  shows "snd (transform_states_aux n m states ! st) x = interp_pexp (m (n + st) x) (snd (states ! st))"
  using assms
  apply (induct states arbitrary: n st)
   apply simp_all
  using less_Suc_eq_0_disj by auto

lemma charact_transform_states_fst[simp]:
  "fst (transform_states_aux n m states ! st) = fst (states ! st)"
  apply (induct states arbitrary: n st)
   apply simp_all
  by (simp add: nth_Cons')

lemma charact_transform_exp:
  assumes "wf_exp nv (length states) e"
  shows "interp_exp vals states (transform_exp m e) = interp_exp vals (transform_states m states) e"
  using assms
proof (induct e arbitrary: vals states)
  case (EPVar st x)
  then have "interp_pexp (m st x) (snd (states ! st)) = snd (transform_states m states ! st) x"
    by (simp add: charact_transform_states_snd)
  then show "interp_exp vals states (transform_exp m (EPVar st x)) = interp_exp vals (transform_states m states) (EPVar st x)"
    by (metis interp_exp.simps(1) same_syn_sem_exp transform_exp.simps(1))
qed (auto)



fun shift_map_and_update :: "(nat \<Rightarrow> 'a substitution) \<Rightarrow> 'a substitution \<Rightarrow> nat \<Rightarrow> 'a substitution" where
  "shift_map_and_update _ subst 0 = subst"
| "shift_map_and_update m _ (Suc n) = m n"


lemma transform_states_aux_shift_map_and_update[simp]:
  "transform_states_aux (Suc n) (shift_map_and_update m subst) states = transform_states_aux n m states"
  by (induct states arbitrary: n) simp_all


fun transform_post_based_on_list :: "(nat \<Rightarrow> 'a substitution) \<Rightarrow> (('a path_condition \<times> 'a substitution) list) \<Rightarrow> 'a assertion \<Rightarrow> 'a assertion"
  where
  "transform_post_based_on_list m L (AForallState A) = AForallState (foldr
  (\<lambda>(pc, subst) B. AAnd B (AImp (pbexp_to_assertion 0 pc) (transform_post_based_on_list (shift_map_and_update m subst) L A)))
  L (AConst True))"

| "transform_post_based_on_list m L (AExistsState A) = AExistsState (foldr
  (\<lambda>(pc, subst) B. AOr B (AAnd (pbexp_to_assertion 0 pc) (transform_post_based_on_list (shift_map_and_update m subst) L A)))
  L (AConst False))"

| "transform_post_based_on_list m L (AExists A) = AExists (transform_post_based_on_list m L A)"
| "transform_post_based_on_list m L (AForall A) = AForall (transform_post_based_on_list m L A)"
| "transform_post_based_on_list m L (AOr A B) = AOr (transform_post_based_on_list m L A) (transform_post_based_on_list m L B)"
| "transform_post_based_on_list m L (AAnd A B) = AAnd (transform_post_based_on_list m L A) (transform_post_based_on_list m L B)"
| "transform_post_based_on_list m L (AConst b) = AConst b"
| "transform_post_based_on_list m L (AComp e1 cmp e2) = AComp (transform_exp m e1) cmp (transform_exp m e2)"


lemma sat_assertion_foldr_and:
  assumes "sat_assertion vals states (foldr (\<lambda>x B. AAnd B (f x)) l (AConst True)) S"
      and "x \<in> set l"
    shows "sat_assertion vals states (f x) S"
  using assms
  apply (induct l)
   apply simp_all
  by blast

lemma sat_assertion_foldr_or:
  assumes "sat_assertion vals states (foldr (\<lambda>x B. AOr B (f x)) l (AConst False)) S"
    shows "\<exists>x \<in> set l. sat_assertion vals states (f x) S"
  using assms
  apply (induct l)
   apply simp_all
  by blast


lemma shift_and_update_charact:
  "transform_states (shift_map_and_update m subst) ((l, \<sigma>) # states) = ((l, apply_substitution subst \<sigma>) # transform_states m states)"
  unfolding apply_substitution_def
  by simp


lemma main_result_aux:
  assumes "sat_assertion vals states (transform_post_based_on_list m L P) S"
      and "wf_assertion_aux (length vals) (length states) P"
  shows "sat_assertion vals (transform_states m states) P {(l, apply_substitution subst \<sigma>) |l \<sigma> subst pc. (l, \<sigma>) \<in> S \<and> (pc, subst) \<in> set L \<and> interp_pbexp pc \<sigma>}"
  using assms
proof (induct P arbitrary: vals states m)
  case (AComp e1 cmp e2)
  then have "cmp (interp_exp vals states (transform_exp m e1)) (interp_exp vals states (transform_exp m e2))"
    by simp
  then have "cmp (interp_exp vals (transform_states m states) e1) (interp_exp vals (transform_states m states) e2)"
    by (metis AComp.prems(2) charact_transform_exp wf_assertion_aux.simps(2))
  then show "sat_assertion vals (transform_states m states) (AComp e1 cmp e2) {(l, apply_substitution subst \<sigma>) |l \<sigma> subst pc. (l, \<sigma>) \<in> S \<and> (pc, subst) \<in> set L \<and> interp_pbexp pc \<sigma>}"
    by auto
next
  case (AForallState P)
  show ?case
  proof clarsimp
    fix l \<sigma> subst pc
    assume asm0: "(l, \<sigma>) \<in> S" "(pc, subst) \<in> set L" "interp_pbexp pc \<sigma>"
    then have "sat_assertion vals ((l, \<sigma>) # states) (foldr
  (\<lambda>(pc, subst) B. AAnd B (AImp (pbexp_to_assertion 0 pc) (transform_post_based_on_list (shift_map_and_update m subst) L P)))
  L (AConst True)) S"
      using AForallState(2) by fastforce

    then have "sat_assertion vals ((l, \<sigma>) # states) (AImp (pbexp_to_assertion 0 pc) (transform_post_based_on_list (shift_map_and_update m subst) L P)) S"
      using sat_assertion_foldr_and[of vals "(l, \<sigma>) # states" "\<lambda>(pc, subst). (AImp (pbexp_to_assertion 0 pc) (transform_post_based_on_list (shift_map_and_update m subst) L P))" L S "(pc, subst)"]
      asm0
    proof -
      have "(\<lambda>p. case p of (p, f) \<Rightarrow> \<lambda>a. AAnd a (AImp (pbexp_to_assertion 0 p) (transform_post_based_on_list (shift_map_and_update m f) L P))) = (\<lambda>p a. AAnd a (case p of (p, f) \<Rightarrow> AImp (pbexp_to_assertion 0 p) (transform_post_based_on_list (shift_map_and_update m f) L P)))"
        by auto
      then show ?thesis
        using \<open>(pc, subst) \<in> set L\<close> \<open>\<lbrakk>sat_assertion vals ((l, \<sigma>) # states) (foldr (\<lambda>x B. AAnd B (case x of (pc, subst) \<Rightarrow> AImp (pbexp_to_assertion 0 pc) (transform_post_based_on_list (shift_map_and_update m subst) L P))) L (AConst True)) S; (pc, subst) \<in> set L\<rbrakk> \<Longrightarrow> sat_assertion vals ((l, \<sigma>) # states) (case (pc, subst) of (pc, subst) \<Rightarrow> AImp (pbexp_to_assertion 0 pc) (transform_post_based_on_list (shift_map_and_update m subst) L P)) S\<close> \<open>sat_assertion vals ((l, \<sigma>) # states) (foldr (\<lambda>(pc, subst) B. AAnd B (AImp (pbexp_to_assertion 0 pc) (transform_post_based_on_list (shift_map_and_update m subst) L P))) L (AConst True)) S\<close> by auto
    qed
(* our state satisfies the pc *)
    then have "sat_assertion vals ((l, \<sigma>) # states) (transform_post_based_on_list (shift_map_and_update m subst) L P) S"
      by (metis asm0(3) nth_Cons_0 prod.sel(2) same_syn_sem_assertion sat_assertion_Imp)
    then have "sat_assertion vals (transform_states (shift_map_and_update m subst) ((l, \<sigma>) # states)) P
{(l, apply_substitution subst \<sigma>) |l \<sigma> subst. (l, \<sigma>) \<in> S \<and> (\<exists>pc. (pc, subst) \<in> set L \<and> interp_pbexp pc \<sigma>)}"
      using AForallState(1)[of vals "((l, \<sigma>) # states)" "shift_map_and_update m subst"]
      using AForallState.prems(2) by force
    then show "sat_assertion vals ((l, apply_substitution subst \<sigma>) # transform_states m states) P
        {(l, apply_substitution subst \<sigma>) |l \<sigma> subst. (l, \<sigma>) \<in> S \<and> (\<exists>pc. (pc, subst) \<in> set L \<and> interp_pbexp pc \<sigma>)}"
      by (metis shift_and_update_charact)
  qed
next
  case (AExistsState P)
  then obtain l \<sigma> where "(l, \<sigma>) \<in> S" "sat_assertion vals ((l, \<sigma>) # states) (foldr
  (\<lambda>(pc, subst) B. AOr B (AAnd (pbexp_to_assertion 0 pc) (transform_post_based_on_list (shift_map_and_update m subst) L P)))
  L (AConst False)) S" by fastforce
  then obtain pc subst where "(pc, subst) \<in> set L"
    "sat_assertion vals ((l, \<sigma>) # states) (AAnd (pbexp_to_assertion 0 pc) (transform_post_based_on_list (shift_map_and_update m subst) L P)) S"
    using sat_assertion_foldr_or[of vals "((l, \<sigma>) # states)" "\<lambda>(pc, subst). AAnd (pbexp_to_assertion 0 pc) (transform_post_based_on_list (shift_map_and_update m subst) L P)" L S]
    by (metis (no_types, lifting) foldr_cong prod.collapse split_def)
  then have "interp_pbexp pc \<sigma> \<and> sat_assertion vals ((l, \<sigma>) # states) (transform_post_based_on_list (shift_map_and_update m subst) L P) S"
    using same_syn_sem_assertion by force
  then have "sat_assertion vals (transform_states (shift_map_and_update m subst) ((l, \<sigma>) # states)) P
 {(l, apply_substitution subst \<sigma>) |l \<sigma> subst. (l, \<sigma>) \<in> S \<and> (\<exists>pc. (pc, subst) \<in> set L \<and> interp_pbexp pc \<sigma>)}"
    using AExistsState(1)[of vals "((l, \<sigma>) # states)" "shift_map_and_update m subst"]
    using AExistsState.prems(2) by auto
  then show ?case
    using \<open>(l, \<sigma>) \<in> S\<close> \<open>(pc, subst) \<in> set L\<close> \<open>interp_pbexp pc \<sigma> \<and> sat_assertion vals ((l, \<sigma>) # states) (transform_post_based_on_list (shift_map_and_update m subst) L P) S\<close> shift_and_update_charact by fastforce
next
  case (AExists P)
  then show ?case
    by fastforce
qed (auto)




theorem main_result:
  assumes "correct_characterizer L C"
      and "wf_assertion P"
  shows "\<Turnstile> {interp_assert (transform_post_based_on_list (\<lambda>_. identity_substitution) L P) } C { interp_assert P }"
proof (rule hyper_hoare_tripleI)
  fix S assume asm0: "interp_assert (transform_post_based_on_list (\<lambda>_. identity_substitution) L P) S"
  moreover have "sem C S = {(l, apply_substitution subst \<sigma>) |l \<sigma> subst pc. (l, \<sigma>) \<in> S \<and> (pc, subst) \<in> set L \<and> interp_pbexp pc \<sigma>}"
    using assms correct_characterizer_sem_charact by blast
  ultimately show "interp_assert P (sem C S)"
    using assms main_result_aux by fastforce
qed



section \<open>Compositionally computing this characterizer\<close>


fun apply_substitution_pexp :: "'a substitution \<Rightarrow> 'a pexp \<Rightarrow> 'a pexp" where
  "apply_substitution_pexp subst (PVar x) = subst x"
| "apply_substitution_pexp subst (PBinop p1 op p2) = PBinop (apply_substitution_pexp subst p1) op (apply_substitution_pexp subst p2)"
| "apply_substitution_pexp subst (PFun f p) = PFun f (apply_substitution_pexp subst p)"
| "apply_substitution_pexp subst (PConst c) = PConst c"

lemma apply_substitution_pexp_charact:
  "interp_pexp (apply_substitution_pexp subst e) \<sigma> = interp_pexp e (apply_substitution subst \<sigma>)"
  by (induct e) (simp_all add: apply_substitution_def)

definition compose_substs :: "'a substitution \<Rightarrow> 'a substitution \<Rightarrow> 'a substitution" where
  "compose_substs subst1 subst2 x = apply_substitution_pexp subst1 (subst2 x)"

fun apply_substitution_pbexp :: "'a substitution \<Rightarrow> 'a pbexp \<Rightarrow> 'a pbexp" where
  "apply_substitution_pbexp subst (PBConst b) = PBConst b"
| "apply_substitution_pbexp subst (PBAnd pb1 pb2) = PBAnd (apply_substitution_pbexp subst pb1) (apply_substitution_pbexp subst pb2)"
| "apply_substitution_pbexp subst (PBOr pb1 pb2) = PBOr (apply_substitution_pbexp subst pb1) (apply_substitution_pbexp subst pb2)"
| "apply_substitution_pbexp subst (PBComp p1 cmp p2) = PBComp (apply_substitution_pexp subst p1) cmp (apply_substitution_pexp subst p2)"

lemma apply_substitution_pbexp_charact:
  "interp_pbexp (apply_substitution_pbexp subst p) \<sigma> \<longleftrightarrow> interp_pbexp p (apply_substitution subst \<sigma>)"
  apply (induct p)
  apply simp_all
  by (simp add: apply_substitution_pexp_charact)

definition compose_pcs :: "'a substitution \<Rightarrow> 'a path_condition \<Rightarrow> 'a path_condition \<Rightarrow> 'a path_condition" where
  "compose_pcs subst1 pc1 pc2 = PBAnd pc1 (apply_substitution_pbexp subst1 pc2)"

definition compose_characterizers :: "'a characterizer \<Rightarrow> 'a characterizer \<Rightarrow> 'a characterizer" where
  "compose_characterizers L1 L2 = map (\<lambda>(r1, r2). (compose_pcs (snd r1) (fst r1) (fst r2), compose_substs (snd r1) (snd r2))) (List.product L1 L2)"

lemma compose_subst_apply:
  "apply_substitution (compose_substs subst1 subst2) \<sigma> = apply_substitution subst2 (apply_substitution subst1 \<sigma>)"
  unfolding compose_substs_def apply_substitution_def
proof (rule ext)
  fix x
  have "interp_pexp (apply_substitution_pexp subst1 (subst2 x)) \<sigma> = interp_pexp (subst2 x) (apply_substitution subst1 \<sigma>)"
    using apply_substitution_pexp_charact by auto
  then show "interp_pexp (apply_substitution_pexp subst1 (subst2 x)) \<sigma> = interp_pexp (subst2 x) (\<lambda>x. interp_pexp (subst1 x) \<sigma>)"
    unfolding apply_substitution_def by blast
qed

lemma map_product:
  assumes "x1 \<in> set l1"
      and "x2 \<in> set l2"
    shows "f (x1, x2) \<in> set (map f (List.product l1 l2))"
proof -
  have "(x1, x2) \<in> set (List.product l1 l2)"
    by (simp add: assms(1) assms(2))
  then show ?thesis
    by force
qed

lemma map_product_reciprocal:
  assumes "r \<in> set (map f (List.product l1 l2))"
  shows "\<exists>x1 x2. x1 \<in> set l1 \<and> x2 \<in> set l2 \<and> r = f (x1, x2)"
proof -
  obtain xx where "xx \<in> set (List.product l1 l2)" "r = f xx"
    using assms by auto
  then show ?thesis by auto
qed

lemma compose_characterizers_valid_seq_comp:
  assumes "correct_characterizer L1 C1"
      and "correct_characterizer L2 C2"
    shows "correct_characterizer (compose_characterizers L1 L2) (C1;; C2)"
proof (rule correct_characterizerI)          
  fix \<sigma> \<sigma>'
  assume asm0: "\<langle>C1 ;; C2, \<sigma>\<rangle> \<rightarrow> \<sigma>'"
  then obtain \<sigma>'' where \<sigma>''_def: "\<langle>C1, \<sigma>\<rangle> \<rightarrow> \<sigma>''" "\<langle>C2, \<sigma>''\<rangle> \<rightarrow> \<sigma>'" by auto
  then obtain pc1 subst1 where "(pc1, subst1) \<in> set L1" "interp_pbexp pc1 \<sigma>" "\<sigma>'' = apply_substitution subst1 \<sigma>"
    by (smt (verit) assms(1) case_prodE correct_characterizer_def)
  moreover obtain pc2 subst2 where "(pc2, subst2) \<in> set L2" "interp_pbexp pc2 \<sigma>''" "\<sigma>' = apply_substitution subst2 \<sigma>''"
    using \<sigma>''_def assms(2)
    by (smt (verit, ccfv_threshold) case_prodE correct_characterizer_def)
  moreover have "(compose_pcs subst1 pc1 pc2, compose_substs subst1 subst2) \<in> set (compose_characterizers L1 L2)"
    unfolding compose_characterizers_def 
    using \<open>(pc1, subst1) \<in> set L1\<close> \<open>(pc2, subst2) \<in> set L2\<close>
    using map_product[of "(pc1, subst1)" L1 "(pc2, subst2)" L2]
    by force
  moreover have "\<sigma>' = apply_substitution (compose_substs subst1 subst2) \<sigma>"
    by (simp add: calculation(3) calculation(6) compose_subst_apply)
  moreover have "interp_pbexp (compose_pcs subst1 pc1 pc2) \<sigma>"
    by (metis apply_substitution_pbexp_charact calculation(2) calculation(3) calculation(5) compose_pcs_def interp_pbexp.simps(2))
  ultimately show "\<exists>(pc, subst)\<in>set (compose_characterizers L1 L2). interp_pbexp pc \<sigma> \<and> \<sigma>' = apply_substitution subst \<sigma>"
    by blast
next
  fix \<sigma> \<sigma>' pc subst
  assume asm0: "(pc, subst) \<in> set (compose_characterizers L1 L2)" "interp_pbexp pc \<sigma>" "\<sigma>' = apply_substitution subst \<sigma>"
  then obtain pc1 pc2 subst1 subst2 where "(pc1, subst1) \<in> set L1" "(pc2, subst2) \<in> set L2"
    "pc = compose_pcs subst1 pc1 pc2" "subst = compose_substs subst1 subst2"
    unfolding compose_characterizers_def
    using map_product_reciprocal[of "(pc, subst)" _ L1 L2]
    by auto
  then have "\<langle>C1, \<sigma>\<rangle> \<rightarrow> apply_substitution subst1 \<sigma>"
    by (metis (mono_tags, lifting) asm0(2) assms(1) case_prodI compose_pcs_def correct_characterizer_def interp_pbexp.simps(2))
  moreover have "\<langle>C2, apply_substitution subst1 \<sigma>\<rangle> \<rightarrow> apply_substitution subst2 (apply_substitution subst1 \<sigma>)"
    by (metis (mono_tags, lifting) \<open>(pc2, subst2) \<in> set L2\<close> \<open>pc = compose_pcs subst1 pc1 pc2\<close> apply_substitution_pbexp_charact asm0(2) assms(2) case_prodI compose_pcs_def correct_characterizer_def interp_pbexp.simps(2))
  ultimately show "\<langle>C1 ;; C2, \<sigma>\<rangle> \<rightarrow> \<sigma>'"
    by (simp add: SemSeq \<open>subst = compose_substs subst1 subst2\<close> asm0(3) compose_subst_apply)
qed


lemma compose_choice:
  assumes "correct_characterizer L1 C1"
      and "correct_characterizer L2 C2"
    shows "correct_characterizer (L1 @ L2) (If C1 C2)"
  apply (rule correct_characterizerI)
  apply (metis Un_iff assms(1) assms(2) correct_characterizer_def set_append single_sem_If_elim)
  apply (case_tac "(pc, subst) \<in> set L1")
  apply (metis (mono_tags, lifting) SemIf1 assms(1) case_prodI correct_characterizer_def)
  by (metis (mono_tags, lifting) SemIf2 Un_iff assms(2) case_prodI correct_characterizer_def set_append)


lemma characterizer_assume:
  "correct_characterizer [(b, identity_substitution)] (Assume (interp_pbexp b))"
  apply (rule correct_characterizerI)
  apply simp_all
  apply (metis identity_substitution_is_identity single_sem_Assume_elim)
  by (simp add: SemAssume identity_substitution_is_identity)

lemma characterizer_assign:
  "correct_characterizer [(PBConst True, identity_substitution(x := p))] (Assign x (interp_pexp p))"
  apply (rule correct_characterizerI)
   apply (elim single_sem_Assign_elim)
  unfolding apply_substitution_def identity_substitution_def
   apply simp_all
   apply fastforce
proof -
  fix \<sigma>
  have "\<langle>Assign x (interp_pexp p), \<sigma>\<rangle> \<rightarrow> \<sigma>(x := interp_pexp p \<sigma>)"
    using SemAssign[of x "interp_pexp p" \<sigma>] by blast
  moreover have "\<sigma>(x := interp_pexp p \<sigma>) = (\<lambda>xa. interp_pexp (if xa = x then p else PVar xa) \<sigma>)"
    apply (rule ext)
    by auto
  ultimately show "\<langle>Assign x (interp_pexp p), \<sigma>\<rangle> \<rightarrow> \<lambda>xa. interp_pexp (if xa = x then p else PVar xa) \<sigma>"
    by simp
qed

lemma characterizer_Skip:
  "correct_characterizer [(PBConst True, identity_substitution)] Skip"
  apply (rule correct_characterizerI)
   apply (elim single_sem_Skip_elim)
  unfolding apply_substitution_def identity_substitution_def
   apply simp_all
  by (simp add: SemSkip)

end