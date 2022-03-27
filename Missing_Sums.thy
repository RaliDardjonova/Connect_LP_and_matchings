theory Missing_Sums
  imports  Linear_Inequalities.Integer_Hull
    Jordan_Normal_Form.Missing_VectorSpace
begin

context gram_schmidt
begin

lemma nonneg_each_smaller_than_sum:
  fixes c :: "'b \<Rightarrow> 'a :: trivial_conjugatable_linordered_field" 
  assumes "finite S" 
  assumes "\<forall>i \<in> S. c i \<ge> 0" 
  shows "\<forall>i \<in> S. c i \<le> sum c S" 
  using member_le_sum[of _ S c]  assms by auto

lemma nonneg_sum_range_each_le:
  fixes f :: "nat \<Rightarrow> 'a"
  assumes "\<forall>i < m. f i \<ge> 0"
  shows "\<forall>i < m. f i \<le> sum f {0..<m}"
  using nonneg_each_smaller_than_sum[of "{0..<m}" f] 
  by (meson assms atLeastLessThan_iff finite_atLeastLessThan zero_le)

lemma sum_range_divided_at_zero:
  fixes f :: "nat \<Rightarrow> 'a :: trivial_conjugatable_linordered_field"
  shows "f 0 + sum f {1..<k +1} = sum f {0..<k+1}" 
  by (auto simp: sum.atLeast_Suc_lessThan)

lemma sumlist_map_carr:
  assumes "f : set A \<rightarrow> carrier_vec n"
  shows "sumlist (map f A) \<in> carrier_vec n" 
proof -
  have "set (map f A) \<subseteq> carrier_vec  n"
    using  Pi_mem 
    using assms by auto
  then show ?thesis 
    using M.sumlist_carrier by blast
qed

lemma sumlist_map_mult:
  assumes "f : set xs \<rightarrow> carrier_vec n"
  assumes "k \<noteq> 0"
  shows "sumlist (map f xs) =  k \<cdot>\<^sub>v sumlist (map (\<lambda>i. (1/k)\<cdot>\<^sub>v(f i)) xs)"
  using assms(1-2)
proof(induct xs)
  case (Cons a xs)
  have f_carr: "f \<in> set xs \<rightarrow> carrier_vec n" 
    using Cons.prems(1) by auto
  have " k \<cdot>\<^sub>v ((\<lambda>i. 1 / k \<cdot>\<^sub>v f i) a + sumlist (map (\<lambda>i. 1 / k \<cdot>\<^sub>v f i) xs)) =
     k \<cdot>\<^sub>v ((\<lambda>i. 1 / k \<cdot>\<^sub>v f i) a) + k \<cdot>\<^sub>v (sumlist (map (\<lambda>i. 1 / k \<cdot>\<^sub>v f i) xs))" 
    apply(rule smult_add_distrib_vec[of _ n])
     apply(auto) 
    using Cons.prems(1)
     apply(auto simp: Pi_mem)
    apply (rule sumlist_map_carr) 
    using f_carr by blast
  then show ?case 
    by (simp add: Cons.hyps assms(2) f_carr smult_smult_assoc)
qed simp

lemma lincomb_in_integer_set:
  assumes "set xs \<subseteq> carrier_vec n"
  assumes "set xs \<subseteq> P \<inter> \<int>\<^sub>v"
  assumes "P = integer_hull P"
  assumes "sum c {0..<length xs} = 1"
  assumes "(\<forall>i<length xs. 0 \<le> c i) " 
  shows "lincomb_list c xs \<in> P" 
proof -
  have "convex_lincomb_list c xs (lincomb_list c xs)" 
    unfolding convex_lincomb_list_def nonneg_lincomb_list_def 
    using assms(5) assms(4) by blast
  have "convex_hull (set xs) = convex_hull_list xs" 
    using assms(1) finite_convex_hull_iff_convex_hull_list by auto
  then have "lincomb_list c xs \<in> convex_hull (set xs)" 
    unfolding convex_hull_list_def 
    using \<open>convex_lincomb_list c xs (lincomb_list c xs)\<close> by blast
  have "convex_hull (set xs) \<subseteq> convex_hull (P \<inter> \<int>\<^sub>v)" 
    using assms(2) convex_hull_mono by presburger
  then show "lincomb_list c xs \<in> P" 
    using \<open>lincomb_list c xs \<in> convex_hull (set xs)\<close> assms(3) integer_hull_def by blast
qed

lemma sumlist_swap_upd_same:
  assumes "set xs \<subseteq> carrier_vec n"
  assumes "i < length xs"
  assumes "j < length xs"
  shows "sumlist (xs[i:= xs ! j, j:= xs ! i]) = sumlist xs" 
  by (auto simp: sumlist_as_summset assms perm_swap)

lemma dqwd:
  shows "map f (x#xs) = f x # (map f xs)" 
  by auto

lemma ff:
  assumes "m > 0" 
  shows "0 # [1..< m] = [0..<m]"
  using upt_eq_Cons_conv[of 0 m 0 "[1..< m]"]
  by (auto simp: assms)

lemma nmdo:
  fixes xs :: "'a vec list" 
  assumes "i < length xs"
  assumes "j < length xs"
  shows "(map (f(i:=f j, j := f i))[0..<length (xs[i := xs ! j, j := xs ! i])]) =
      (map f [0..<length xs])[i := (map f [0..<length xs]) ! j, j := (map f [0..<length xs]) ! i]"
  by (simp add: assms  map_nth_eq_conv)

lemma swap_fun_nonneg:
  assumes "i < length xs"
  assumes "j < length xs"
  assumes "\<forall>ia < length xs. 0 \<le> f ia" 
  assumes "ia < length xs"
  shows "0 \<le> (f(i := f j, j := f i)) ia"
  using assms by auto

lemma sum_of_swap_fun_eq:
  assumes "finite A"
  assumes "i \<in> A"
  assumes "j \<in> A"
  shows "sum (f(i := f j, j := f i)) A = sum f A"
proof -
  let ?g = "(f(i := f j, j := f i))" 
  have "{i, j} \<subseteq> A" 
    using assms(2) assms(3) by blast
  have sum_union_f: "sum f A = sum f (A - {i, j}) + sum f {i, j}"
    by (intro sum.subset_diff[of "{i, j}" A f] assms(1) `{i, j} \<subseteq> A` )
  have sum_union_g: "sum ?g A = sum ?g (A - {i, j}) + sum ?g {i, j}"
    by (intro sum.subset_diff[of "{i, j}" A ?g] assms(1) `{i, j} \<subseteq> A` )
  show "sum (f(i := f j, j := f i)) A = sum f A"
    apply(simp only:sum_union_f sum_union_g)
    by (cases "i = j"; auto simp: add.commute)
qed   

lemma sum_swap_is_one:
  assumes "finite (set xs)"
  assumes "i < length xs"
  assumes "j < length xs"
  assumes "sum c {0..<length xs} = 1"
  shows " sum (c(i := c j, j := c i)) {0..<length xs} = 1"
  using sum_of_swap_fun_eq[of "{0..<length xs}" i j c] assms 
  by fastforce

lemma zero_vec_is_int:
  shows "0\<^sub>v n \<in>  \<int>\<^sub>v" 
  unfolding Ints_vec_def zero_vec_def 
  by fastforce

lemma sum_int_is_int:
  assumes "a \<in> carrier_vec n"
  assumes "b \<in> carrier_vec n"
  assumes "a \<in> \<int>\<^sub>v"
  assumes "b \<in> \<int>\<^sub>v"
  shows "a + b \<in> \<int>\<^sub>v" 
  using assms unfolding Ints_vec_def by force

lemma sumlist_map_append:
  assumes "f : {0..<Suc m} \<rightarrow> carrier_vec n"
  shows "sumlist (map f [0..<Suc m]) = sumlist (map f [0..<m]) + f m"
  using sumlist_snoc[of "(map f [0..<m])" "f m"] assms 
  by force

lemma sumlist_of_ints_is_int:
  assumes "f : {0..<m} \<rightarrow> carrier_vec n"
  assumes "\<forall>j < m. f  j \<in> \<int>\<^sub>v"
  shows "sumlist (map f [0..<m]) \<in> \<int>\<^sub>v"
  using assms 
proof(induct m)
  case (Suc m)
  have f_carr:"f \<in> {0..<m} \<rightarrow> carrier_vec n" 
    using Suc.prems(1) by auto
  have sum_carr:"sumlist (map f [0..<m]) \<in> carrier_vec n" 
    by  (auto simp: sumlist_map_carr f_carr)
  show ?case
    apply (simp only: sumlist_map_append[of f m] Suc.prems(1))
    apply(intro sum_int_is_int)
    using sum_carr  apply blast
    using Suc.prems(1) apply auto
    using Suc.hyps f_carr  Suc.prems(2) less_Suc_eq apply presburger
    by (simp add: Suc.prems(2))
qed (simp add: zero_vec_is_int)

lemma sum_mono_nonneg:
  fixes f :: "'b \<Rightarrow> 'a"
  assumes "finite S"
  assumes "\<forall>i \<in> S. f i \<ge> 0" 
  assumes "F \<subseteq> S"
  shows "sum f F \<le> sum f S" 
  using sum_mono2[of S F f] assms DiffD1 
  by blast

lemma sum_eq_one_elem_other_zero:
  fixes f :: "'b \<Rightarrow> 'a"
  assumes "finite S" 
  assumes "\<forall>i \<in> S. f i \<ge> 0" 
  assumes "i \<in> S"
  assumes "f i = sum f S"
  assumes "j \<in> S \<and> j \<noteq> i"
  shows "f j = 0"
proof(rule ccontr)
  assume "f j \<noteq> 0" 
  then have "f j > 0" 
    using assms(2) assms(5) dual_order.order_iff_strict by blast
  have "sum f {i, j} \<le> sum f S" using sum_mono_nonneg[of S f "{i, j}"] 
    using assms(1) assms(2) assms(3) assms(5) by fastforce
  then show False using assms `f j > 0`
    by force
qed

lemma int_mult_int_vec:
  assumes "a \<in> \<int>\<^sub>v" 
  assumes "k \<in> \<int>"
  shows "k \<cdot>\<^sub>v a \<in> \<int>\<^sub>v" 
  using assms(1) assms(2) indexed_Ints_vec_UNIV smult_indexed_Ints_vec by blast

lemma convex_lincom_int:
  assumes "convex_lincomb_list c L x"
  assumes "set L \<subseteq> \<int>\<^sub>v"  
  assumes "set L \<subseteq> carrier_vec n"
  assumes "\<forall>i < length L. c i \<in> \<int>"
  shows "x \<in> \<int>\<^sub>v"
proof -
  have "\<forall>j < length L. (\<lambda>i. c i \<cdot>\<^sub>v L ! i)  j \<in> \<int>\<^sub>v" 
    using assms(2) assms(4) nth_mem int_mult_int_vec by blast
  then have "sumlist (map (\<lambda>i. c i \<cdot>\<^sub>v L ! i) [0..<length L]) \<in>  \<int>\<^sub>v" 
    using sumlist_of_ints_is_int[of "(\<lambda>i. c i \<cdot>\<^sub>v L ! i)" "length L"] assms(3) by fastforce
  then show "x \<in> \<int>\<^sub>v" 
    using assms(1) 
    unfolding convex_lincomb_list_def lincomb_list_def nonneg_lincomb_list_def
    by blast
qed

lemma convex_lincomb_less_1_coeff:
  fixes x :: "'a :: trivial_conjugatable_linordered_field vec"
  assumes "convex_lincomb_list c L x"
  assumes "x \<notin> \<int>\<^sub>v"
  assumes "set L \<subseteq> \<int>\<^sub>v"  
  assumes "set L \<subseteq> carrier_vec n" 
  assumes "i < length L" 
  shows "c i < 1" 
proof -
  have fin:"finite (set L)" 
    by simp
  have nonneg_sum_1: "(\<forall> i < length L. c i \<ge> 0) \<and> sum c {0..<length L} = 1" 
    using assms(1) convex_lincomb_list_def nonneg_lincomb_list_def by blast
  show "c i < 1" 
  proof(rule ccontr)
    assume " \<not> c i < 1" 
    then have "c i = 1"
      using  nonneg_sum_range_each_le[of "length L" c] 
        assms(5) nonneg_sum_1 order_le_imp_less_or_eq 
      by metis
    have "\<forall>j < length L. i \<noteq> j \<longrightarrow> c j = 0" 
      using sum_eq_one_elem_other_zero[of "{0..<length L}" c i] 
      by (auto simp: \<open>c i = 1\<close> assms(5) nonneg_sum_1) 
    then have "x \<in> \<int>\<^sub>v" using convex_lincom_int[of c L x] 
      by (metis Ints_0 Ints_1 \<open>c i = 1\<close> assms(1) assms(3) assms(4))
    then show False 
      by (simp add: assms(2))
  qed
qed

lemma map_shift_by_one: 
  "(map (\<lambda>i. f i \<cdot>\<^sub>v (a # ax) ! i) [1..<length (a # ax)]) = 
    (map (\<lambda> i. (f (i+1)) \<cdot>\<^sub>v ax ! i) [0..<length ax])"
proof -
  have append_shift:"\<forall> i < length ax. ([Suc 0..<length ax] @ [length ax]) ! i = i + 1" 
    using nth_upt[of 1 _ "length ax + 1"] by auto
  have "(map (\<lambda> i. (f (i+1) \<cdot>\<^sub>v (a # ax) ! (i+1))) [0..<length ax]) = 
    (map (\<lambda> i. (f i \<cdot>\<^sub>v (a # ax) ! i)) [1..<length ax + 1])"
    apply (auto simp: map_eq_conv' append_shift) 
    by (metis Suc_leI length_greater_0_conv)
  then show ?thesis
    by auto
qed

end
end