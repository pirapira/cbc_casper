theory BetsAndValidators

imports Main

begin

datatype validator = Validator int

type_synonym weight = "validator \<Rightarrow> int"

definition tie_breaking :: "validator set \<Rightarrow> weight \<Rightarrow> bool"
where
"tie_breaking V w =
 ( \<forall> S0 S1.
    S0 \<subseteq> V \<longrightarrow>
    S1 \<subseteq> V \<longrightarrow>
    S0 \<noteq> S1 \<longrightarrow>
    sum w S0 \<noteq> sum w S1
 )"

definition uniform_weight :: "validator \<Rightarrow> int" 
where
"uniform_weight v = 1"

lemma should_be_false: "\<not> tie_breaking {Validator 0, Validator 1} uniform_weight "
apply(simp add: tie_breaking_def)
apply(rule_tac x = "{Validator 1}" in exI)
apply simp
apply(rule_tac x = "{Validator 0}" in exI)
apply (simp add: uniform_weight_def)
done

datatype estimate = Estimate bool

datatype bet =
  Bet "estimate * validator * bet list"

fun sender :: "bet \<Rightarrow> validator"
where
"sender (Bet (_, v, _)) = v"

fun est :: "bet \<Rightarrow> estimate"
where
"est (Bet (e, _, _)) = e"

fun justifies :: "bet \<Rightarrow> (bet \<Rightarrow> bool)"
where
"justifies b (Bet (e, v, js)) = (b \<in> set js)"


inductive tran :: "(bet \<Rightarrow> bet \<Rightarrow> bool) \<Rightarrow> (bet \<Rightarrow> bet \<Rightarrow> bool)"
where
  tran_simple: "R x y \<Longrightarrow> tran R x y"
| tran_composit: "tran R x y \<Longrightarrow> R y z \<Longrightarrow> tran R x z"


lemma tran_cases :
"tran R x z = (R x z \<or> (\<exists> y. R y z \<and> tran R x y))"
by (metis tran.simps)


definition is_dependency :: "bet \<Rightarrow> bet \<Rightarrow> bool"
where
"is_dependency = tran justifies"

(*
lemma justifies_antisymmetric:
  "\<not> justifies b b"
sledgehammer
*)

lemma is_dependency_tail_first :
  "tran R y z \<Longrightarrow> R x y \<Longrightarrow> tran R x z"
apply(induction rule: tran.induct)
  apply (meson tran_cases)
	using tran_composit by blast


(* no cycle *)
lemma dependency_no_cycle :
  "\<forall> a. is_dependency a b \<longrightarrow> \<not> is_dependency b a"
apply(induction b)
apply(simp add: is_dependency_def)
apply(rule allI)
apply(rule impI)
apply(subgoal_tac "tran justifies a (Bet xa)  = (justifies a (Bet xa) \<or> (\<exists> y. justifies y (Bet xa) \<and> tran justifies a y))" )
 defer
 using tran_cases apply blast
apply auto
by (meson is_dependency_tail_first justifies.simps)

lemma dependency_is_transitive :
  "is_dependency y z \<Longrightarrow> \<forall> x. is_dependency x y \<longrightarrow> is_dependency x z"
apply(simp add: is_dependency_def)
apply(induction rule: tran.induct)
 using tran_composit apply blast
using tran_composit by blast


definition equivocation :: "bet \<Rightarrow> bet \<Rightarrow> bool"
where
"equivocation b0 b1 =
   (sender b0 = sender b1 \<and> \<not> is_dependency b0 b1 \<and> \<not> is_dependency b1 b0 \<and> b0 \<noteq> b1 )"

definition is_view :: "bet set \<Rightarrow> bool"
where
"is_view bs = (\<forall> b0 b1. b0 \<in> bs \<longrightarrow> b1 \<in> bs \<longrightarrow> \<not> equivocation b0 b1)"

definition latest_bets :: "bet set \<Rightarrow> validator \<Rightarrow> bet set"
where
" latest_bets bs v = { l . l \<in> bs \<and> sender l = v \<and> (\<not> (\<exists> b'. b' \<in> bs \<and> sender b' = v \<and> is_dependency l b')) } "

definition is_latest_in :: "bet \<Rightarrow> bet set \<Rightarrow> bool"
where
"is_latest_in b bs = (b \<in> bs \<and> (\<not> (\<exists> b'. b' \<in> bs \<and> is_dependency b b')))"

lemma latest_bets_are_latest_in :
"(latest_bets bs v) = {b. (is_latest_in b {b' . b' \<in> bs \<and> sender b' = v})}"
apply(auto simp add: is_latest_in_def latest_bets_def)
done

definition is_non_empty :: "'a set \<Rightarrow> bool"
where
"is_non_empty bs =
  ( \<exists>b. b\<in>bs )"

lemma latest_existence' :
  "finite bs \<Longrightarrow> is_non_empty bs \<longrightarrow> (\<exists> l. is_latest_in l bs)"
apply(rule finite_induct)
  apply simp
 apply (simp add: is_non_empty_def)
apply(case_tac "is_non_empty F")
 defer
 apply(simp add: is_non_empty_def)
 apply(rule_tac x = x in exI)
 using dependency_no_cycle is_latest_in_def apply auto[1]
apply auto
apply(case_tac "is_dependency l x")
 defer
 apply(rule_tac x = l in exI)
 using is_latest_in_def apply auto[1]
apply(rule_tac x = x in exI)
apply(auto simp add: is_latest_in_def)
 using dependency_no_cycle apply blast
using dependency_is_transitive by blast

lemma latest_existence :
  "finite bs \<Longrightarrow> is_non_empty bs \<Longrightarrow> (\<exists> l. is_latest_in l bs)"
using latest_existence' by auto

lemma two_latests_are_equivocation :
  "b0 \<in> latest_bets bs v \<Longrightarrow> b1 \<in> latest_bets bs v \<Longrightarrow> b0 \<noteq> b1 \<Longrightarrow> equivocation b0 b1"
apply(simp add: equivocation_def latest_bets_def)
done


definition at_most_one :: "'a set \<Rightarrow> bool"
where
"at_most_one s = (\<forall> x y. x \<in> s \<longrightarrow> y \<in> s \<longrightarrow> x = y)"

lemma view_has_at_most_one_latest_bet :
  "is_view bs \<Longrightarrow>
   at_most_one (latest_bets bs v)"
apply(auto simp add: at_most_one_def is_view_def)
apply(drule_tac x = x in spec)
apply(subgoal_tac "x \<in> bs")
 apply simp
 apply(drule_tac x = y in spec)
 apply(subgoal_tac "y \<in> bs")
  apply simp
  using two_latests_are_equivocation apply fastforce
 apply(auto simp add: latest_bets_def)
done

(*
by (meson at_most_one_def is_view_def latest_bets_def mem_Collect_eq two_latests_are_equivocation)
*)


lemma should_be_not_be_non_empty :
  "\<not>is_non_empty {}"
by(simp add: is_non_empty_def)

definition observed_validators :: "bet set \<Rightarrow> validator set" 
where 
  "observed_validators bs =
({v :: validator. \<exists>b. b \<in> bs \<and> v = sender b })"
  
lemma observed_validators_exist_in_non_empty_bet_set :
  "is_non_empty bs \<Longrightarrow> is_non_empty (observed_validators bs)"
by (simp add: is_non_empty_def observed_validators_def)

lemma observed_validator_has_latest_bet :
  "finite bs \<longrightarrow> v \<in> (observed_validators bs) \<longrightarrow> is_non_empty (latest_bets bs v)"
apply(simp add: is_non_empty_def observed_validators_def)
apply(simp add: latest_bets_are_latest_in)
apply clarify
apply(rule latest_existence)
 apply auto
using is_non_empty_def by blast
  
lemma latest_bets_exist_in_non_empty_bet_set :
  "finite bs \<Longrightarrow>
   is_non_empty bs \<Longrightarrow>
  \<exists>v::validator.(is_non_empty (latest_bets bs v))
   "
by (meson is_non_empty_def observed_validator_has_latest_bet observed_validators_exist_in_non_empty_bet_set)

definition has_a_latest_bet_on :: "bet set \<Rightarrow> validator \<Rightarrow> estimate \<Rightarrow> bool"
where
"has_a_latest_bet_on bs v e =
 (\<exists> b. b \<in> latest_bets bs v \<and> est b = e)"

lemma validator_in_view_contributes_to_at_most_one_estimates_weight :
  "is_view bs \<Longrightarrow>
   \<forall>v. v\<in>(observed_validators bs) \<longrightarrow> at_most_one {e. (has_a_latest_bet_on bs v e)}
  "
apply(auto simp add: has_a_latest_bet_on_def at_most_one_def)
apply(drule_tac v = v in view_has_at_most_one_latest_bet)
apply(auto simp add: at_most_one_def)
done


definition weight_of_estimate :: "bet set \<Rightarrow> weight \<Rightarrow> estimate \<Rightarrow> int"
where
"weight_of_estimate bs w e =
 sum w { v. has_a_latest_bet_on bs v e }"

definition is_max_weight_estimate :: "bet set \<Rightarrow> weight \<Rightarrow> estimate \<Rightarrow> bool"
where
"is_max_weight_estimate bs w e =
  (\<forall> e'.
   weight_of_estimate bs w e \<ge> weight_of_estimate bs w e')
 "


definition positive_weights :: "validator set \<Rightarrow> weight \<Rightarrow> bool"
where
"positive_weights vs w =
  (\<forall>v. v \<in> vs \<longrightarrow> w v > 0)
"

lemma finite_observed_validators :
  "finite bs \<Longrightarrow> finite (observed_validators bs)"
apply(simp add: observed_validators_def)
done

lemma some_bets_imply_some_validators :
  "is_non_empty bs \<Longrightarrow> is_non_empty (observed_validators bs)"
by (simp add: observed_validators_exist_in_non_empty_bet_set)

lemma finite_latest_betters_if_only_finite_bets :
 "finite bs \<Longrightarrow>
  finite {v. has_a_latest_bet_on bs v e}"
apply(simp add: has_a_latest_bet_on_def latest_bets_def)
done

lemma any_latest_bet_witnesses_a_validator:
  "Bet (e, v', js) \<in> latest_bets bs v \<Longrightarrow> {v. has_a_latest_bet_on bs v e} \<noteq> {}"
apply(auto simp add: latest_bets_def has_a_latest_bet_on_def)
done

lemma latest_bets_have_positive_weights :
   "finite bs \<Longrightarrow>
    positive_weights (observed_validators bs) w \<Longrightarrow>
    Bet (e, v', js) \<in> latest_bets bs v \<Longrightarrow>
    weight_of_estimate bs w e > 0"
apply(auto simp add: weight_of_estimate_def)
apply(rule Groups_Big.ordered_comm_monoid_add_class.sum_pos)
  apply(simp add: finite_latest_betters_if_only_finite_bets)
 using any_latest_bet_witnesses_a_validator apply blast
using has_a_latest_bet_on_def latest_bets_def observed_validators_def positive_weights_def by auto

lemma non_empty_bet_set_has_non_zero_weight_for_some_estimate :
  "finite bs \<Longrightarrow>
   is_non_empty bs \<Longrightarrow>
   positive_weights (observed_validators bs) w \<Longrightarrow>
   \<exists>e. weight_of_estimate bs w e > 0"
apply(subgoal_tac "
  \<exists>v::validator.(is_non_empty (latest_bets bs v))")
 defer
 using latest_bets_exist_in_non_empty_bet_set apply auto[1]
apply(auto simp add: is_non_empty_def)
apply(case_tac ba)
apply(case_tac x)
apply simp
using latest_bets_have_positive_weights by blast

lemma tie_breaking_contra :
    "tie_breaking vs w \<Longrightarrow>
     sum w vs0 = sum w vs1 \<Longrightarrow>
     vs0 \<subseteq> vs \<Longrightarrow>
     vs1 \<subseteq> vs \<Longrightarrow>
     vs0 = vs1"
using tie_breaking_def by blast

lemma only_observed_validators_can_bet_latest_bets :
  "{v. has_a_latest_bet_on bs v x} \<subseteq> observed_validators bs"
apply(auto simp add: has_a_latest_bet_on_def latest_bets_def observed_validators_def)
done

lemma latest_bets_are_same :
  "is_view bs \<Longrightarrow> b \<in> latest_bets bs v \<Longrightarrow> ba \<in> latest_bets bs v \<Longrightarrow> b = ba"
by (meson at_most_one_def view_has_at_most_one_latest_bet)

lemma latest_bets_are_on_same_estimate:
   "is_view bs \<Longrightarrow> has_a_latest_bet_on bs v y 
   \<Longrightarrow> has_a_latest_bet_on bs v x
   \<Longrightarrow> x = y"
apply(auto simp add: has_a_latest_bet_on_def)
using latest_bets_are_same by auto


lemma tie_breaking_validators_put_same_weight_only_on_same_estimate :
 "is_view bs \<Longrightarrow>
  tie_breaking (observed_validators bs) w \<Longrightarrow>
  0 < weight_of_estimate bs w x \<Longrightarrow>
  weight_of_estimate bs w x = weight_of_estimate bs w y \<Longrightarrow> x = y"
proof (simp add: weight_of_estimate_def)
 assume "tie_breaking (observed_validators bs) w"
 moreover assume " sum w {v. has_a_latest_bet_on bs v x} = sum w {v. has_a_latest_bet_on bs v y}"
 ultimately have "{v. has_a_latest_bet_on bs v x} = {v. has_a_latest_bet_on bs v y}"
  using only_observed_validators_can_bet_latest_bets tie_breaking_contra by blast
 moreover assume "0 < sum w {v. has_a_latest_bet_on bs v y}"
 moreover assume "is_view bs"
 ultimately show "x = y"
  proof -
   assume "0 < sum w {v. has_a_latest_bet_on bs v y}"
   then have "\<exists> v. v \<in> {v. has_a_latest_bet_on bs v y}"
    proof -
    	have "\<not> sum w {v. has_a_latest_bet_on bs v y} \<le> 0"
  	  	using \<open>0 < sum w {v. has_a_latest_bet_on bs v y}\<close> by force
  	  then show ?thesis
  	  	by (meson sum_nonpos)
    qed
   moreover assume "{v. has_a_latest_bet_on bs v x} = {v. has_a_latest_bet_on bs v y}"
   ultimately have "\<exists> v. v \<in> {v. has_a_latest_bet_on bs v y} \<and> v \<in> {v. has_a_latest_bet_on bs v x}"
    by blast
   then have "\<exists> v. has_a_latest_bet_on bs v y \<and> has_a_latest_bet_on bs v x"
    by blast
   moreover assume "is_view bs"
   ultimately show "x = y"
    using latest_bets_are_on_same_estimate by blast
  qed
qed

lemma non_empty_bets_have_positive_weighted_estimate :
  "finite bs \<Longrightarrow>
   is_non_empty bs \<Longrightarrow>
   positive_weights (observed_validators bs) w \<Longrightarrow>
   \<exists> e'. sum w {v. has_a_latest_bet_on bs v e'} > 0"
using non_empty_bet_set_has_non_zero_weight_for_some_estimate weight_of_estimate_def by auto

lemma tmp:
 "\<exists> e'. sum (w :: validator \<Rightarrow> int) {v. has_a_latest_bet_on bs v e'} > 0 \<Longrightarrow>
  \<forall>e'. sum w {v. has_a_latest_bet_on bs v e'} \<le> 0 \<Longrightarrow> False"
apply(erule exE)
apply(drule_tac x = e' in spec)
by auto


lemma max_weight_is_positive :
  "finite bs \<Longrightarrow>
   is_non_empty bs \<Longrightarrow>
   positive_weights (observed_validators bs) w \<Longrightarrow>
   \<forall>e'. weight_of_estimate bs w e' \<le> weight_of_estimate bs w x \<Longrightarrow>
   0 < weight_of_estimate bs w x"
apply(auto simp add: weight_of_estimate_def)
apply(case_tac "sum w {v. has_a_latest_bet_on bs v x} = 0"; simp)
 using non_empty_bets_have_positive_weighted_estimate tmp apply blast
proof -
  assume a1: "positive_weights (observed_validators bs) w"
  assume a2: "sum w {v. has_a_latest_bet_on bs v x} \<noteq> 0"
  have f3: "\<forall>v. v \<notin> observed_validators bs \<or> \<not> w v \<le> 0"
    using a1 positive_weights_def by fastforce
  obtain vv :: "(validator \<Rightarrow> int) \<Rightarrow> validator set \<Rightarrow> validator" where
    "\<forall>x0 x1. (\<exists>v2. v2 \<in> x1 \<and> \<not> 0 \<le> x0 v2) = (vv x0 x1 \<in> x1 \<and> \<not> 0 \<le> x0 (vv x0 x1))"
    by moura
  then have f4: "\<forall>V f. vv f V \<in> V \<and> \<not> 0 \<le> f (vv f V) \<or> 0 \<le> sum f V"
  by (meson sum_nonneg)
  obtain bb :: "estimate \<Rightarrow> validator \<Rightarrow> bet set \<Rightarrow> bet" where
    "\<forall>x0 x1 x2. (\<exists>v3. v3 \<in> latest_bets x2 x1 \<and> est v3 = x0) = (bb x0 x1 x2 \<in> latest_bets x2 x1 \<and> est (bb x0 x1 x2) = x0)"
    by moura
  then have f5: "(\<not> has_a_latest_bet_on bs (vv w {v. has_a_latest_bet_on bs v x}) x \<or> bb x (vv w {v. has_a_latest_bet_on bs v x}) bs \<in> latest_bets bs (vv w {v. has_a_latest_bet_on bs v x}) \<and> est (bb x (vv w {v. has_a_latest_bet_on bs v x}) bs) = x) \<and> (has_a_latest_bet_on bs (vv w {v. has_a_latest_bet_on bs v x}) x \<or> (\<forall>b. b \<notin> latest_bets bs (vv w {v. has_a_latest_bet_on bs v x}) \<or> est b \<noteq> x))"
    using has_a_latest_bet_on_def by auto
  have "(bb x (vv w {v. has_a_latest_bet_on bs v x}) bs \<notin> bs \<or> sender (bb x (vv w {v. has_a_latest_bet_on bs v x}) bs) \<noteq> vv w {v. has_a_latest_bet_on bs v x} \<or> (\<exists>b. b \<in> bs \<and> sender b = vv w {v. has_a_latest_bet_on bs v x} \<and> is_dependency (bb x (vv w {v. has_a_latest_bet_on bs v x}) bs) b)) \<or> (bb x (vv w {v. has_a_latest_bet_on bs v x}) bs \<notin> bs \<or> sender (bb x (vv w {v. has_a_latest_bet_on bs v x}) bs) \<noteq> vv w {v. has_a_latest_bet_on bs v x} \<or> (\<exists>b. b \<in> bs \<and> sender b = vv w {v. has_a_latest_bet_on bs v x} \<and> is_dependency (bb x (vv w {v. has_a_latest_bet_on bs v x}) bs) b)) \<or> (\<exists>b. b \<in> bs \<and> vv w {v. has_a_latest_bet_on bs v x} = sender b)"
    by (metis (no_types))
  moreover
  { assume aa1: "\<exists>b. b \<in> bs \<and> vv w {v. has_a_latest_bet_on bs v x} = sender b"
    have "w (vv w {uu. has_a_latest_bet_on bs uu x}) \<le> 0 \<or> 0 \<le> w (vv w {uu. has_a_latest_bet_on bs uu x})"
      by linarith
    then have "sum w {v. has_a_latest_bet_on bs v x} \<noteq> 0 \<and> 0 \<le> sum w {v. has_a_latest_bet_on bs v x}"
      using aa1 f4 f3 a2 observed_validators_def by auto }
  moreover
  { assume "\<not> (bb x (vv w {v. has_a_latest_bet_on bs v x}) bs \<in> bs \<and> sender (bb x (vv w {v. has_a_latest_bet_on bs v x}) bs) = vv w {v. has_a_latest_bet_on bs v x} \<and> (\<forall>b. b \<notin> bs \<or> sender b \<noteq> vv w {v. has_a_latest_bet_on bs v x} \<or> \<not> is_dependency (bb x (vv w {v. has_a_latest_bet_on bs v x}) bs) b))"
    then have "\<not> has_a_latest_bet_on bs (vv w {v. has_a_latest_bet_on bs v x}) x"
      using f5 latest_bets_def by blast
    then have "sum w {v. has_a_latest_bet_on bs v x} \<noteq> 0 \<and> 0 \<le> sum w {v. has_a_latest_bet_on bs v x}"
      using f4 a2 by (meson mem_Collect_eq) }
  ultimately have "sum w {v. has_a_latest_bet_on bs v x} \<noteq> 0 \<and> 0 \<le> sum w {v. has_a_latest_bet_on bs v x}"
    by blast
  then show "0 < (\<Sum>v | has_a_latest_bet_on bs v x. w v)"
    by linarith
qed

lemma weight_of_estimate_anti_symmetric :
  "\<forall>e'. weight_of_estimate bs w e' \<le> weight_of_estimate bs w x \<Longrightarrow>
   \<forall>e'. weight_of_estimate bs w e' \<le> weight_of_estimate bs w y \<Longrightarrow>
   weight_of_estimate bs w x = weight_of_estimate bs w y"
(* sledgehammer *)
proof -
  assume a1: "\<forall>e'. weight_of_estimate bs w e' \<le> weight_of_estimate bs w y"
  assume a2: "\<forall>e'. weight_of_estimate bs w e' \<le> weight_of_estimate bs w x"
  have "weight_of_estimate bs w x = weight_of_estimate bs w y \<or> \<not> weight_of_estimate bs w x + - 1 * weight_of_estimate bs w y \<le> 0 \<or> \<not> 0 \<le> weight_of_estimate bs w x + - 1 * weight_of_estimate bs w y"
    by auto
  then show ?thesis
    using a2 a1 by simp
qed

(* prove view \<Longrightarrow> tie breaking \<Rightarrow> non empty \<Rightarrow> exists at most one max estimate *)
lemma view_has_at_most_one_max_weight_estimate :
  "is_view bs \<Longrightarrow>
   finite bs \<Longrightarrow>
   is_non_empty bs \<Longrightarrow>
   positive_weights (observed_validators bs) w \<Longrightarrow>
   tie_breaking (observed_validators bs) w \<Longrightarrow>
   at_most_one {e. is_max_weight_estimate bs w e}"
apply(auto simp add: is_max_weight_estimate_def at_most_one_def)
apply(rule_tac bs = bs and w = w in tie_breaking_validators_put_same_weight_only_on_same_estimate)
   apply blast
  apply blast
 apply(simp add: max_weight_is_positive)
using weight_of_estimate_anti_symmetric by blast
  
declare is_max_weight_estimate_def [simp]

lemma "is_max_weight_estimate {} f e = True"
apply(simp add: weight_of_estimate_def)
apply(simp add: has_a_latest_bet_on_def latest_bets_def)
done

fun is_valid :: "weight \<Rightarrow> bet \<Rightarrow> bool"
where
"is_valid w (Bet (e, v, js)) = is_max_weight_estimate (set js) w e"

definition is_valid_view :: "weight \<Rightarrow> bet set \<Rightarrow> bool"
where
"is_valid_view w bs = (is_view bs \<and> (\<forall> b \<in> bs. is_valid w b))"

definition is_future_view :: "weight \<Rightarrow> bet set \<Rightarrow> bet set \<Rightarrow> bool"
where
"is_future_view w b0 b1 =
 (b0 \<supseteq> b1 \<and> is_valid_view w b0 \<and> is_valid_view w b1)"

definition is_estimate_safe :: "weight \<Rightarrow> bet set \<Rightarrow> estimate \<Rightarrow> bool"
where
"is_estimate_safe w bs e =
 (\<forall> bf. is_future_view w bf bs \<longrightarrow> is_max_weight_estimate bf w e)"

definition consistent_views :: "weight \<Rightarrow> bet set \<Rightarrow> bet set \<Rightarrow> bool"
where
"consistent_views w b0 b1 =
 (is_valid_view w b0 \<and> is_valid_view w b1 \<and> is_valid_view w (b0 \<union> b1))"

lemma union_of_consistent_views_is_future :
  "consistent_views w b0 b1 \<Longrightarrow>
   is_future_view w (b0 \<union> b1) b0"
apply(auto simp add: consistent_views_def is_future_view_def is_valid_view_def)
done

lemma positive_weights_on_union_of_bets :
  "positive_weights (observed_validators b0) w \<Longrightarrow>
   positive_weights (observed_validators b1) w \<Longrightarrow>
   positive_weights (observed_validators (b0 \<union> b1)) w"
apply(auto simp add: positive_weights_def observed_validators_def)
done


lemma consensus_safety :
  "finite b0 \<Longrightarrow>
   finite b1 \<Longrightarrow>
   is_non_empty b0 \<Longrightarrow>
   is_non_empty b1 \<Longrightarrow>
   positive_weights (observed_validators b0) w \<Longrightarrow>
   positive_weights (observed_validators b1) w \<Longrightarrow>
   tie_breaking (observed_validators (b0 \<union> b1)) w \<Longrightarrow>
   is_estimate_safe w b0 e0 \<Longrightarrow>
   is_estimate_safe w b1 e1 \<Longrightarrow>
   consistent_views w b0 b1 \<Longrightarrow>
   e0 = e1
  "
proof -
  assume "consistent_views w b0 b1"
  then have "is_future_view w (b0 \<union> b1) b0"
    using union_of_consistent_views_is_future by blast
  moreover assume "is_estimate_safe w b0 e0"
  ultimately have max0: "is_max_weight_estimate (b0 \<union> b1) w e0"
    by (simp add: is_estimate_safe_def)

  assume "consistent_views w b0 b1"
  then have "consistent_views w b1 b0"
    by (simp add: consistent_views_def sup.commute)
  then have "is_future_view w (b1 \<union> b0) b1"
    using union_of_consistent_views_is_future by blast
  moreover assume "is_estimate_safe w b1 e1"
  ultimately have "is_max_weight_estimate (b1 \<union> b0) w e1"
    by (simp add: is_estimate_safe_def)
  then have max1: "is_max_weight_estimate (b0 \<union> b1) w e1"
    by (simp add: sup_commute)

  assume f0: "finite b0"
  moreover assume f1: "finite b1"
  moreover assume e0: "is_non_empty b0"
  moreover assume e1: "is_non_empty b1"
  moreover assume p0: "positive_weights (observed_validators b0) w"
  moreover assume p1: "positive_weights (observed_validators b1) w"
  moreover assume t: "tie_breaking (observed_validators (b0 \<union> b1)) w"
  ultimately have
   unique: "at_most_one {e. is_max_weight_estimate (b0 \<union> b1) w e}"
    proof -
      show "at_most_one {e. is_max_weight_estimate (b0 \<union> b1) w e}"
      apply(rule view_has_at_most_one_max_weight_estimate)
         apply (metis Un_commute \<open>is_future_view w (b1 \<union> b0) b1\<close> is_future_view_def is_valid_view_def)
        apply (simp add: \<open>finite b0\<close> \<open>finite b1\<close>)
       apply (metis \<open>is_non_empty b0\<close> is_non_empty_def set_rev_mp sup.cobounded2 sup.commute)
    	apply (simp add: \<open>positive_weights (observed_validators b0) w\<close> \<open>positive_weights (observed_validators b1) w\<close> positive_weights_on_union_of_bets)
     by (simp add: t)
    qed
  show "e0 = e1"
by (meson at_most_one_def max0 max1 mem_Collect_eq unique)
qed

(*

compute estimate_safety
by
adversary on the weaker model

*)

end
