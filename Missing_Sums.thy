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

lemma sum_range_divided_at_zero:
  fixes f :: "nat \<Rightarrow> 'a :: trivial_conjugatable_linordered_field"
  shows "f 0 + sum f {1..<k +1} = sum f {0..<k+1}" 
  by (auto simp: sum.atLeast_Suc_lessThan)


lemma fhghg:
  fixes f :: "nat \<Rightarrow> 'a :: trivial_conjugatable_linordered_field  vec"
  assumes "f : set xs \<rightarrow> carrier_vec n"
  assumes "k \<noteq> 0"
  shows "sumlist (map f xs) =  k \<cdot>\<^sub>v sumlist (map (\<lambda>i. (1/k)\<cdot>\<^sub>v(f i)) xs)"
  using assms(1-2)
proof(induct xs)
  case (Cons a xs)

  have "f \<in> set xs \<rightarrow> carrier_vec n" 
    using Cons.prems(1) by auto
  have "M.sumlist (map f xs) = k \<cdot>\<^sub>v M.sumlist (map (\<lambda>i. 1 / k \<cdot>\<^sub>v f i) xs)" 
    using Cons.hyps Cons.prems(1) `f \<in> set xs \<rightarrow> carrier_vec n` `k \<noteq> 0` 
    by blast
  have "sumlist (map f (a # xs)) = f a + sumlist (map f xs)" 
    by simp
  have "k \<cdot>\<^sub>v sumlist (map (\<lambda>i. 1 / k \<cdot>\<^sub>v f i) (a # xs)) =
    k \<cdot>\<^sub>v ((\<lambda>i. 1 / k \<cdot>\<^sub>v f i) a + sumlist (map (\<lambda>i. 1 / k \<cdot>\<^sub>v f i) xs))" 
    by fastforce
  have "( 1 / k \<cdot>\<^sub>v f a) \<in> carrier_vec n" 
    using Cons.prems(1) 
    by (simp add: Pi_mem)
  have "set (map (\<lambda>i. 1 / k \<cdot>\<^sub>v f i) xs) \<subseteq> carrier_vec  n"
     using Cons.prems(1) Pi_mem 
    by auto
  then  have "(sumlist (map (\<lambda>i. 1 / k \<cdot>\<^sub>v f i) xs)) \<in> carrier_vec  n" 
    by force
    then have " k \<cdot>\<^sub>v ((\<lambda>i. 1 / k \<cdot>\<^sub>v f i) a + sumlist (map (\<lambda>i. 1 / k \<cdot>\<^sub>v f i) xs)) =
     k \<cdot>\<^sub>v ((\<lambda>i. 1 / k \<cdot>\<^sub>v f i) a) + k \<cdot>\<^sub>v (sumlist (map (\<lambda>i. 1 / k \<cdot>\<^sub>v f i) xs))" 
      using smult_add_distrib_vec  using Cons.prems(1) Pi_mem 
      using \<open>1 / k \<cdot>\<^sub>v f a \<in> carrier_vec n\<close> by blast

  have "  k \<cdot>\<^sub>v ((\<lambda>i. 1 / k \<cdot>\<^sub>v f i) a) = f a" using assms(2) 
    by fastforce
  then show ?case 
    using \<open>M.sumlist (map f (a # xs)) = f a + M.sumlist (map f xs)\<close> \<open>M.sumlist (map f xs) = k \<cdot>\<^sub>v M.sumlist (map (\<lambda>i. 1 / k \<cdot>\<^sub>v f i) xs)\<close> \<open>k \<cdot>\<^sub>v (1 / k \<cdot>\<^sub>v f a + M.sumlist (map (\<lambda>i. 1 / k \<cdot>\<^sub>v f i) xs)) = k \<cdot>\<^sub>v (1 / k \<cdot>\<^sub>v f a) + k \<cdot>\<^sub>v M.sumlist (map (\<lambda>i. 1 / k \<cdot>\<^sub>v f i) xs)\<close> \<open>k \<cdot>\<^sub>v M.sumlist (map (\<lambda>i. 1 / k \<cdot>\<^sub>v f i) (a # xs)) = k \<cdot>\<^sub>v (1 / k \<cdot>\<^sub>v f a + M.sumlist (map (\<lambda>i. 1 / k \<cdot>\<^sub>v f i) xs))\<close> by presburger
qed simp


lemma jlewfweg:
  fixes ax :: "'a :: trivial_conjugatable_linordered_field vec list"
  assumes "finite (set ax)"
  assumes "set ax \<subseteq> carrier_vec n"
  assumes "set ax \<subseteq> P \<inter> \<int>\<^sub>v"
  assumes "P = integer_hull P"
  assumes "sum c {0..<length ax} = 1"
  assumes "(\<forall>i<length ax. 0 \<le> c i) " 
  shows "sumlist ( map (\<lambda>i. c i \<cdot>\<^sub>v ax ! i) [0..<length ax]) \<in> P" 
proof -
  let ?z = "sumlist ( map (\<lambda>i. c i \<cdot>\<^sub>v ax ! i) [0..<length ax])" 
  have "lincomb_list c ax = sumlist (map (\<lambda>i. c i \<cdot>\<^sub>v ax ! i) [0..<length ax])" 
     using lincomb_list_def by blast
   then have "nonneg_lincomb_list c ax ?z" 
     using assms(6) nonneg_lincomb_list_def by blast 
   then have "convex_lincomb_list c ax ?z" 
     using assms(5) convex_lincomb_list_def by blast
   have "convex_hull (set ax) = convex_hull_list ax" 
     using assms(2) finite_convex_hull_iff_convex_hull_list by auto
   then have "?z \<in> convex_hull (set ax)" 
     using \<open>convex_lincomb_list c ax (M.sumlist (map (\<lambda>i. c i \<cdot>\<^sub>v ax ! i) [0..<length ax]))\<close> convex_hull_list_def by blast
   then have "convex_hull (set ax) \<subseteq> convex_hull (P \<inter> \<int>\<^sub>v)" 
     using assms(3) convex_hull_mono by presburger
   then show "?z \<in> P" 
     using assms(4) unfolding integer_hull_def using `?z \<in> convex_hull (set ax)` 
     by blast 
 qed

lemma mvdryy:
  fixes f :: "nat \<Rightarrow> 'a"
  assumes "sum f {0..<m} = 1"
  assumes "\<forall>i < m. f i \<ge> 0"
  shows "\<forall>i < m. f i \<le> 1" 
  using nonneg_each_smaller_than_sum
  by (metis assms(1) assms(2) atLeastLessThan_iff finite_atLeastLessThan zero_le)

lemma lfff:
  fixes xs :: "'a vec list" 
  assumes "set xs \<subseteq> carrier_vec n"
  assumes "i < length xs"
  assumes "j < length xs"
  shows "sumlist (xs[i:= xs ! j, j:= xs ! i]) =sumlist xs" 
proof -
  have "sumlist xs = summset (mset xs)" using sumlist_as_summset
    using assms(1) by auto
  have "sumlist (xs[i:= xs ! j, j:= xs ! i]) = 
      summset (mset (xs[i:= xs ! j, j:= xs ! i]))"
using sumlist_as_summset
    using assms(1) 
    using assms(2) assms(3) set_swap by blast
  have "mset (xs[i:= xs ! j, j:= xs ! i]) =  mset xs"
    by (simp add: assms(2) assms(3) perm_swap)
  then show ?thesis 
    using \<open>M.sumlist (xs[i := xs ! j, j := xs ! i]) = M.summset (mset (xs[i := xs ! j, j := xs ! i]))\<close> \<open>M.sumlist xs = M.summset (mset xs)\<close> by presburger
qed

end
end