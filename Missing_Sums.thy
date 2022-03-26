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

lemma mvdryy:
  fixes f :: "nat \<Rightarrow> 'a"
  assumes "\<forall>i < m. f i \<ge> 0"
  shows "\<forall>i < m. f i \<le> sum f {0..<m}"
  using nonneg_each_smaller_than_sum
  by (metis assms(1) atLeastLessThan_iff finite_atLeastLessThan zero_le)

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

lemma ohp:
 fixes f :: "'b \<Rightarrow> 'a"
 assumes "finite A" "B \<subseteq> A"
 shows  "sum f (A - B)  + sum f B = sum f A"
  using assms(1) assms(2) sum.subset_diff
  by metis


lemma jkkhhhjl':
  assumes "finite A"
  assumes "i \<in> A"
  assumes "j \<in> A"
  shows "sum (f(i := f j, j := f i)) A = sum f A"
proof -
  let ?g = "(f(i := f j, j := f i))" 
  have "{i, j} \<subseteq> A" 
    using assms(2) assms(3) by blast
  have 1:"sum f A = sum f (A - {i, j}) + sum f {i, j}"
    by (intro sum.subset_diff[of "{i, j}" A f] assms(1) `{i, j} \<subseteq> A` )
 have 2:"sum ?g A = sum ?g (A - {i, j}) + sum ?g {i, j}"
   by (intro sum.subset_diff[of "{i, j}" A ?g] assms(1) `{i, j} \<subseteq> A` )
  then show "sum (f(i := f j, j := f i)) A = sum f A"
    apply(simp only:1 2)
    by (cases "i = j"; auto simp: add.commute)
qed   

(*     apply(insert sum.subset_diff[of"{i, j}" A])
    apply(simp only: assms(1) `{i, j} \<subseteq> A`) 
    oops *)


lemma jkkhhhjl:
  assumes "finite (set xs)"
  assumes "i < length xs"
  assumes "j < length xs"
  assumes "sum c {0..<length xs} = 1"
  shows " sum (c(i := c j, j := c i)) {0..<length xs} = 1"
  using jkkhhhjl'[of "{0..<length xs}" i j c] assms 
  by fastforce

lemma vvwe:
  shows "0\<^sub>v n \<in>  \<int>\<^sub>v" 
  unfolding Ints_vec_def zero_vec_def 
  by fastforce

lemma bjrtj:
  assumes "a \<in> carrier_vec n"
  assumes "b \<in> carrier_vec n"
  assumes "a \<in> \<int>\<^sub>v"
  assumes "b \<in> \<int>\<^sub>v"
  shows "a + b \<in> \<int>\<^sub>v"  
  unfolding Ints_vec_def 
  by (smt (verit, ccfv_SIG) Ints_add Ints_vec_def assms carrier_vecD index_add_vec(1) 
      index_add_vec(2) mem_Collect_eq)



lemma nrtn:
assumes "f : {0..<m} \<rightarrow> carrier_vec n"
  assumes "\<forall>j < m. f  j \<in> \<int>\<^sub>v"
  shows "sumlist (map f [0..<m]) \<in> \<int>\<^sub>v"
  using assms 
proof(induct m)
  case 0
  have "(map f [0..<0]) = []" by auto
  then have "sumlist (map f [0..<0]) = 0\<^sub>v n" 
    using M.sumlist_Nil by presburger
  then show ?case 
    by (simp add: vvwe)
next
  case (Suc m)
  have "f \<in> {0..<m} \<rightarrow> carrier_vec n" 
    using Suc.prems(1) by auto
  have " \<forall>j<m. f j \<in> \<int>\<^sub>v" 
    using Suc.prems(2) less_Suc_eq by presburger
  then have "M.sumlist (map f [0..<m]) \<in> \<int>\<^sub>v" 
    using Suc.hyps \<open>f \<in> {0..<m} \<rightarrow> carrier_vec n\<close> by blast
  
  have "M.sumlist (map f [0..<Suc m]) = sumlist (map f [0..<m]) + f m"
    using sumlist_snoc[of "(map f [0..<m])" "f m"] 
    using Suc.prems(1) 
    by force
  have "f m \<in> \<int>\<^sub>v" using Suc.prems(2) 
    by fast
  have "set (map f [0..<m]) \<subseteq> carrier_vec n"  using Suc.prems(1) by auto
  have "f m \<in> carrier_vec n"  using Suc.prems(1) by auto
  have "sumlist (map f [0..<m]) \<in> carrier_vec n" 
    using M.sumlist_carrier \<open>set (map f [0..<m]) \<subseteq> carrier_vec n\<close> by presburger
  then show ?case using `M.sumlist (map f [0..<Suc m]) = sumlist (map f [0..<m]) + f m` 
      `M.sumlist (map f [0..<m]) \<in> \<int>\<^sub>v` using bjrtj
    by (metis \<open>f m \<in> \<int>\<^sub>v\<close> \<open>f m \<in> carrier_vec n\<close>)
qed

lemma bnter:
fixes x :: "'a :: trivial_conjugatable_linordered_field vec"
  assumes "convex_lincomb_list c Wsl x"
  assumes "x \<notin> \<int>\<^sub>v"
  assumes "set Wsl \<subseteq> \<int>\<^sub>v"  
 assumes "set Wsl \<subseteq> carrier_vec n"  
  shows "\<forall> i < length Wsl. c i < 1" 
proof(rule+)
  fix i
  assume "i < length Wsl" 
  have "finite (set Wsl)" 
    by simp
  have "(\<forall> i < length Wsl. c i \<ge> 0) \<and> sum c {0..<length Wsl} = 1" 
    using assms(1) convex_lincomb_list_def nonneg_lincomb_list_def by blast
  show "c i < 1" 
  proof(rule ccontr)
    assume " \<not> c i < 1" 
    then have "c i =  1" using mvdryy
      by (metis \<open>(\<forall>i<length Wsl. 0 \<le> c i) \<and> sum c {0..<length Wsl} = 1\<close> \<open>i < length Wsl\<close> order_le_imp_less_or_eq)
    have "\<forall>j < length Wsl. i \<noteq> j \<longrightarrow> c j = 0" 
    proof(rule+)
      fix j
      assume "j < length Wsl" 
      assume "i \<noteq> j"
      show "c j = 0"
      proof(rule ccontr)
        assume "c j \<noteq> 0" 
        then have "c j > 0" 
          by (metis \<open>(\<forall>i<length Wsl. 0 \<le> c i) \<and> sum c {0..<length Wsl} = 1\<close> \<open>j < length Wsl\<close> order_le_imp_less_or_eq)
        then have "c j + c i > 1" 
          by (simp add: \<open>c i = 1\<close>)

 have "finite {0..<length Wsl}" 
    by simp
  have "{0..<length Wsl} - {i, j} \<union> {i, j} = {0..<length Wsl}" 
    using `j < length Wsl` `i < length Wsl`  by fastforce
  have "{i, j} - ({0..<length Wsl} - {i, j}) = {i, j}" 
     by fastforce

 then have "sum c {0..<length Wsl} = sum c ({0..<length Wsl} - {i, j})  + sum c {i, j}" 
    using sum_Un2[of "{0..<length Wsl} - {i, j}" "{i, j}" "c"] 
    by (metis Diff_disjoint \<open>finite {0..<length Wsl}\<close> \<open>{0..<length Wsl} - {i, j} \<union> {i, j} = {0..<length Wsl}\<close> finite.emptyI finite.insertI finite_Diff sum.union_disjoint) 
  
  have "sum c ({0..<length Wsl} - {i, j}) \<ge> 0" 
    by (meson DiffD1 \<open>(\<forall>i<length Wsl. 0 \<le> c i) \<and> sum c {0..<length Wsl} = 1\<close> atLeastLessThan_iff sum_nonneg)

  then have "c i + c j \<le> sum c {0..<length Wsl}" 
    using `sum c {0..<length Wsl} = sum c ({0..<length Wsl} - {i, j})  + sum c {i, j}` `i \<noteq> j`
    by simp
  then show False 
    using \<open>(\<forall>i<length Wsl. 0 \<le> c i) \<and> sum c {0..<length Wsl} = 1\<close> \<open>1 < c j + c i\<close> by linarith
qed
qed
  have "\<forall> j < length Wsl. Wsl ! j \<in> carrier_vec n" 
    using assms(4) nth_mem by blast
  then have "\<forall>j<length Wsl. i \<noteq> j \<longrightarrow> c j \<cdot>\<^sub>v Wsl ! j = 0\<^sub>v n" 
    using `\<forall>j<length Wsl. i \<noteq> j \<longrightarrow> c j = 0` 
    by auto
  have "x =  sumlist (map (\<lambda>i. c i \<cdot>\<^sub>v Wsl ! i) [0..<length Wsl])"
    by (metis assms(1) convex_lincomb_list_def lincomb_list_def  nonneg_lincomb_list_def)
  then have "x = sumlist (map (\<lambda>j. if j = i then  c i \<cdot>\<^sub>v Wsl ! i else 0\<^sub>v n) [0..<length Wsl])"
    using `\<forall>j<length Wsl. i \<noteq> j \<longrightarrow> c j \<cdot>\<^sub>v Wsl ! j = 0\<^sub>v n` 
    by (smt (verit, ccfv_SIG) add_0 length_map map_eq_conv' map_nth nth_upt)

  have "(\<lambda>i. c i \<cdot>\<^sub>v Wsl ! i) \<in> {0..<length Wsl} \<rightarrow> carrier_vec n" 
    by (simp add: \<open>\<forall>j<length Wsl. Wsl ! j \<in> carrier_vec n\<close>)
  have "\<forall>j < length Wsl.  (\<lambda>i. c i \<cdot>\<^sub>v Wsl ! i)  j \<in> \<int>\<^sub>v"
  proof(rule)
    fix j
    show " j < length Wsl \<longrightarrow> c j \<cdot>\<^sub>v Wsl ! j \<in> \<int>\<^sub>v"
    proof
      assume " j < length Wsl"
      have "Wsl ! j \<in> \<int>\<^sub>v" 
        using \<open>j < length Wsl\<close> assms(3) nth_mem by blast
      have "c j \<in> \<int>" 
        by (metis Ints_0 Ints_1 \<open>\<forall>j<length Wsl. i \<noteq> j \<longrightarrow> c j = 0\<close> \<open>c i = 1\<close> \<open>j < length Wsl\<close>)
      show " c j \<cdot>\<^sub>v Wsl ! j \<in> \<int>\<^sub>v" 
        by (metis \<open>Wsl ! j \<in> \<int>\<^sub>v\<close> \<open>\<forall>j<length Wsl. i \<noteq> j \<longrightarrow> c j \<cdot>\<^sub>v Wsl ! j = 0\<^sub>v n\<close> \<open>c i = 1\<close> \<open>j < length Wsl\<close> scalar_vec_one vvwe)

    qed
  qed

  then have "sumlist (map (\<lambda>i. c i \<cdot>\<^sub>v Wsl ! i) [0..<length Wsl]) \<in>  \<int>\<^sub>v" 
    using nrtn[of "(\<lambda>i. c i \<cdot>\<^sub>v Wsl ! i)" "length Wsl"]  
    using \<open>(\<lambda>i. c i \<cdot>\<^sub>v Wsl ! i) \<in> {0..<length Wsl} \<rightarrow> carrier_vec n\<close> by blast

  then have "x \<in> \<int>\<^sub>v" 
    using \<open>x = M.sumlist (map (\<lambda>i. c i \<cdot>\<^sub>v Wsl ! i) [0..<length Wsl])\<close> by blast
  then show False 
    by (simp add: assms(2))
qed
qed


lemma aghjk: 
"( map (\<lambda>i. f i \<cdot>\<^sub>v (a # ax) ! i) [1..<length (a # ax)]) = 
      ( map (\<lambda> i. (f (i+1)) \<cdot>\<^sub>v ax ! i) [0..<length ax])"
proof -
  have 1:"\<forall>  i < length ax. ([Suc 0..<length ax] @ [length ax]) ! i = i + 1" 
    using nth_upt[of 1 _ "length ax + 1"] by auto
  have " ( map (\<lambda> i. (f (i+1)) \<cdot>\<^sub>v ax ! i) [0..<length ax]) =
       ( map (\<lambda> i. (f (i+1) \<cdot>\<^sub>v (a # ax) ! (i+1))) [0..<length ax])" 
    by fastforce
   also have "\<dots> = ( map (\<lambda> i. (f i \<cdot>\<^sub>v (a # ax) ! i)) [1..<length ax + 1])"
     apply (auto simp: map_eq_conv' 1)
    by (meson Suc_leI length_greater_0_conv)
  ultimately show ?thesis
    by auto
qed


end
end