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
by (smt at_most_one_def is_view_def latest_bets_def mem_Collect_eq two_latests_are_equivocation)

definition is_non_empty :: "'a set \<Rightarrow> bool"
where
"is_non_empty bs =
  ( \<exists>b. b\<in>bs )
"

lemma should_be_not_be_non_empty :
  "\<not>is_non_empty {}"
by(simp add: is_non_empty_def)

definition observed_validators :: "bet set \<Rightarrow> validator set" 
where 
  "observed_validators bs =
({v :: validator. \<exists>b. b \<in> bs \<longrightarrow> v = sender b })"
  
lemma observed_validators_exist_in_non_empty_bet_set :
  "is_non_empty bs \<Longrightarrow> is_non_empty (observed_validators bs)"
using is_non_empty_def observed_validators_def by auto

lemma observed_validator_has_latest_bet :
  "v \<in> (observed_validators bs) \<longrightarrow> is_non_empty (latest_bets bs v)"
  apply(simp add: is_non_empty_def observed_validators_def)
sorry
  
lemma latest_bets_exist_in_non_empty_bet_set :
  "is_non_empty bs \<Longrightarrow>
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
by(smt at_most_one_def has_a_latest_bet_on_def mem_Collect_eq view_has_at_most_one_latest_bet)

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

(* proof of this lemma is very strange - found using sledgehammer... almost would prefer being 'sorry' *)
lemma finite_observed_validators :
  "finite bs \<Longrightarrow> finite (observed_validators bs)"
apply(simp add: observed_validators_def)
  using is_non_empty_def latest_bets_def observed_validator_has_latest_bet observed_validators_def by fastforce


lemma non_empty_bet_set_has_non_zero_weight_for_some_estimate :
  "is_non_empty bs \<Longrightarrow>
   positive_weights (observed_validators bs) w \<Longrightarrow>
   \<exists>e. weight_of_estimate bs w e > 0"
using is_non_empty_def latest_bets_def observed_validator_has_latest_bet observed_validators_def by fastforce 

(* prove view \<Longrightarrow> tie breaking \<Rightarrow> non empty \<Rightarrow> exists at most one max estimate *)
lemma view_has_at_most_one_max_weight_estimate :
  "is_view bs \<Longrightarrow>
   is_non_empty bs \<Longrightarrow>
   tie_breaking (validator_of ) w \<Longrightarrow>
   at_most_one {e. is_max_weight_estimate bs w e}
   "
using is_non_empty_def latest_bets_def observed_validator_has_latest_bet observed_validators_def by fastforce
  
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

lemma consensus_safety :
  "is_estimate_safe w b0 e0 \<Longrightarrow>
   is_estimate_safe w b1 e1 \<Longrightarrow>
   consistent_views w b0 b1 \<Longrightarrow>
   e0 = e1
  "
proof -
  assume "consistent_views w b0 b1"
  then have "is_future_view w (b0 \<union> b1) b0"
    using union_of_consistent_views_is_future by blast
  moreover assume "is_estimate_safe w b0 e0"
  ultimately have "is_max_weight_estimate (b0 \<union> b1) w e0"
    by (simp add: is_estimate_safe_def)

  assume "consistent_views w b0 b1"
  then have "consistent_views w b1 b0"
    by (simp add: consistent_views_def sup.commute)
  then have "is_future_view w (b1 \<union> b0) b1"
    using union_of_consistent_views_is_future by blast
  moreover assume "is_estimate_safe w b1 e1"
  ultimately have "is_max_weight_estimate (b1 \<union> b0) w e1"
    by (simp add: is_estimate_safe_def)
  then have "is_max_weight_estimate (b0 \<union> b1) w e1"
    by (simp add: sup_commute)

  show "e0 = e1"
     using is_non_empty_def latest_bets_def observed_validator_has_latest_bet observed_validators_def by fastforce


(*

compute estimate_safety
by
adversary on the weaker model

*)

end
