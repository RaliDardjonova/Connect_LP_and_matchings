theory Faces
  imports  Linear_Inequalities.Decomposition_Theorem 
           Linear_Inequalities.Missing_Matrix
           LP_Duality.LP_Duality
          Jordan_Normal_Form.Matrix
          Jordan_Normal_Form.DL_Rank_Submatrix

begin 

definition
  one_vec :: "nat \<Rightarrow> 'a :: one vec" ("1\<^sub>v")
  where "1\<^sub>v n \<equiv> vec n (\<lambda> i. 1)"

lemma one_carrier_vec[simp]: "1\<^sub>v n \<in> carrier_vec n"
  unfolding one_vec_def carrier_vec_def by auto

lemma index_one_vec[simp]: "i < n \<Longrightarrow> 1\<^sub>v n $ i = 1" "dim_vec (1\<^sub>v n) = n"
  unfolding one_vec_def by auto

lemma vec_of_dim_1[simp]: "dim_vec v = 0 \<longleftrightarrow> v = 1\<^sub>v 0" by auto

lemma scalar_prod_left_one[simp]:
  "(v :: 'a :: semiring_1 vec) \<in> carrier_vec n \<Longrightarrow> 1\<^sub>v n \<bullet> v = sum (\<lambda> i. v $ i) {0..<n}"
  unfolding scalar_prod_def 
  by auto

lemma scalar_prod_right_one[simp]: "(v :: 'a :: semiring_1 vec) \<in> carrier_vec n \<Longrightarrow> v \<bullet> 1\<^sub>v n = sum (\<lambda> i. v $ i) {0..<n}"
  unfolding scalar_prod_def
  by auto

context gram_schmidt
begin




definition support_hyp where
  "support_hyp P \<alpha> \<beta> \<equiv> (\<beta> = Maximum { \<alpha> \<bullet> x | x. x \<in> P}) 
                        \<and> has_Maximum { \<alpha> \<bullet> x | x. x \<in> P} 
                       \<and> \<alpha> \<in> carrier_vec n"

definition valid_ineq where
  "valid_ineq P \<alpha> \<beta> \<equiv> (\<forall>x \<in> P. \<alpha> \<bullet> x \<le> \<beta>) \<and> \<alpha> \<in> carrier_vec n" 

lemma support_hyp_elim[elim]:
  assumes "support_hyp P \<alpha> \<beta>"
  shows "\<beta> = Maximum { \<alpha> \<bullet> x | x. x \<in> P}"
        "has_Maximum { \<alpha> \<bullet> x | x. x \<in> P}"
        "\<alpha> \<in> carrier_vec n" 
  using assms
  unfolding support_hyp_def
  by auto

lemma support_hyp_intro[intro]:
  assumes "has_Maximum { \<alpha> \<bullet> x | x. x \<in> P}"
  assumes "\<beta> = Maximum { \<alpha> \<bullet> x | x. x \<in> P}"
  assumes "\<alpha> \<in> carrier_vec n" 
  shows "support_hyp P \<alpha> \<beta>" 
  unfolding support_hyp_def
  using assms 
  by auto

lemma valid_ineq_elim[elim]:
  assumes "valid_ineq P \<alpha> \<beta>"
  shows "\<forall>x \<in> P. \<alpha> \<bullet> x \<le> \<beta>"
        "\<alpha> \<in> carrier_vec n" 
  using assms
  unfolding valid_ineq_def
  by auto

lemma valid_ineq_intro[intro]:
  assumes "\<forall>x \<in> P. \<alpha> \<bullet> x \<le> \<beta>"
  assumes "\<alpha> \<in> carrier_vec n" 
  shows "valid_ineq P \<alpha> \<beta>"
  unfolding valid_ineq_def
  using assms
  by auto

lemma exists_greater_if_not_Maximum:
  assumes "a \<in> A"
  assumes "a \<noteq> Maximum A"
  shows "\<exists> m \<in> A. m > a"
  using assms 
  by (metis assms(2) eqMaximumI leI) 



lemma valid_ineq_non_empty_is_support:
  assumes "valid_ineq P \<alpha> \<beta>"
  assumes "{x. \<alpha> \<bullet> x = \<beta>} \<inter> P \<noteq> {}"
  shows "support_hyp P \<alpha> \<beta>"
proof
  obtain x where "x \<in> P \<and> \<alpha> \<bullet> x = \<beta>" using assms(2) 
    by blast
  then have " \<beta> \<in> {\<alpha> \<bullet> x |x. x \<in> P}"
    by auto
  show "\<beta> = Maximum {\<alpha> \<bullet> x |x. x \<in> P}"
  proof(rule ccontr)
    assume " \<beta> \<noteq> Maximum {\<alpha> \<bullet> x |x. x \<in> P}"
    then have "\<exists> x \<in> P. \<alpha> \<bullet> x > \<beta>" 
      
      by (smt (verit) \<open>\<beta> \<in> {\<alpha> \<bullet> x |x. x \<in> P}\<close> exists_greater_if_not_Maximum mem_Collect_eq)
    then show False using assms(1) 
      by (meson leD valid_ineq_def)
  qed
  show "has_Maximum {\<alpha> \<bullet> x |x. x \<in> P}" 
    using \<open>\<beta> \<in> {\<alpha> \<bullet> x |x. x \<in> P}\<close> assms(1) has_Maximum_def valid_ineq_elim by fast
  show "\<alpha> \<in> carrier_vec n" 
    using assms(1) valid_ineq_elim(2) by blast
qed

lemma support_hyp_is_valid:
  assumes "support_hyp P \<alpha> \<beta>"
  shows  "valid_ineq P \<alpha> \<beta>"
     and "{x. \<alpha> \<bullet> x = \<beta>} \<inter> P \<noteq> {}"
proof
  have "\<beta> = Maximum {\<alpha> \<bullet> x |x. x \<in> P}  \<and> has_Maximum {\<alpha> \<bullet> x |x. x \<in> P}" using assms by force 
  then show "\<forall>x\<in>P. \<alpha> \<bullet> x \<le> \<beta>" 
    using has_MaximumD(2) by blast
  have "\<beta> \<in> {\<alpha> \<bullet> x |x. x \<in> P}" 
    using \<open>\<beta> = Maximum {\<alpha> \<bullet> x |x. x \<in> P} \<and> has_Maximum {\<alpha> \<bullet> x |x. x \<in> P}\<close> has_MaximumD(1) by blast
  then show "{x. \<alpha> \<bullet> x = \<beta>} \<inter> P \<noteq> {}" 
    by blast
  show "\<alpha> \<in> carrier_vec n" 
    using assms support_hyp_elim(3) by blast
qed



definition face :: "'a vec set \<Rightarrow> 'a vec set \<Rightarrow> bool" where
  "face P F \<equiv> P \<noteq> {} \<and> (\<exists> \<alpha> \<beta>. F = P \<inter> {x |x. \<alpha> \<bullet> x = \<beta>} \<and> support_hyp P \<alpha> \<beta> )"



lemma face_elim[elim]:
  assumes "face P F"
  shows "P \<noteq> {}"
    and "(\<exists> \<alpha> \<beta>. F = P \<inter> {x |x. \<alpha> \<bullet> x = \<beta>} \<and> support_hyp P \<alpha> \<beta> )"
  using assms unfolding face_def by auto

lemma face_intro[intro]:
  assumes "P \<noteq> {}"  
  assumes "F = P \<inter> {x |x. \<alpha> \<bullet> x = \<beta>}"
  assumes "support_hyp P \<alpha> \<beta>" 
  shows "face P F" 
  unfolding face_def
  using assms 
  by auto

lemma face_elim2[elim]:
  assumes "face P F"
  shows  "(\<exists> \<alpha> \<beta>. F = P \<inter> {x |x. \<alpha> \<bullet> x = \<beta>} \<and> valid_ineq P \<alpha> \<beta> \<and> F \<noteq> {})"
  using support_hyp_is_valid
  by (smt (verit, del_insts) assms disjoint_iff_not_equal face_elim(2) mem_Collect_eq)

lemma face_intro2[intro]:
  assumes "valid_ineq P \<alpha> \<beta>"
  assumes "F = P \<inter> {x |x. \<alpha> \<bullet> x = \<beta>}"
  assumes "F \<noteq> {}"
  shows "face P F"
  unfolding face_def
  using valid_ineq_non_empty_is_support[of P \<alpha> \<beta>] assms
  by blast

lemma face_non_empty:
  assumes "face P F"
  shows "F \<noteq> {}" 
  using face_elim2  
  using assms by blast

lemma face_subset_polyhedron:
  assumes "face (polyhedron A b) F"
  shows "F \<subseteq> polyhedron A b"
  using assms unfolding face_def 
  by auto

lemma face_is_Max':
  fixes A b
  defines "P \<equiv> polyhedron A b"
  assumes "F = {x. \<alpha> \<bullet> x = \<beta>  \<and> x \<in> P}"
  assumes "valid_ineq P \<alpha> \<beta>"
  assumes "F \<noteq> {}" 
  shows "\<beta> =  Maximum {\<alpha> \<bullet> x | x. x \<in> carrier_vec n \<and> A *\<^sub>v x \<le> b}" (is "\<beta> = Maximum ?Ineq")
  and "has_Maximum {\<alpha> \<bullet> x | x. x \<in> carrier_vec n \<and> A *\<^sub>v x \<le> b}"  (is "has_Maximum ?Ineq")
proof - 
  have "P \<noteq> {}" using assms unfolding face_def by auto
  obtain x where "x \<in> F" using assms(4) by auto
  then have "\<beta> = \<alpha> \<bullet> x" using assms(2) by auto
  have "x \<in> carrier_vec n \<and>  A *\<^sub>v x \<le> b"
    using assms(1) unfolding polyhedron_def 
    using assms(2)
    
    using \<open>x \<in> F\<close> by fastforce
  then have "\<beta> \<in> {\<alpha> \<bullet> x | x. x \<in> carrier_vec n \<and> A *\<^sub>v x \<le> b}"
    using `\<beta> = \<alpha> \<bullet> x` by auto
  then show "\<beta> = Maximum ?Ineq" 
    using assms(3) unfolding valid_ineq_def
    using assms(1) unfolding polyhedron_def 
    by (smt (verit, ccfv_threshold) eqMaximumI mem_Collect_eq)
  show "has_Maximum ?Ineq"   
    by (smt (verit, best) P_def \<open>\<beta> \<in> {\<alpha> \<bullet> x |x. x \<in> carrier_vec n \<and> A *\<^sub>v x \<le> b}\<close> assms(3) gram_schmidt.polyhedron_def has_Maximum_def mem_Collect_eq valid_ineq_elim(1))
qed


lemma face_primal_bounded:
  fixes A b
  defines "P \<equiv> polyhedron A b"
  assumes "valid_ineq P \<alpha> \<beta>"
  shows "\<forall> x \<in> carrier_vec n. A *\<^sub>v x \<le> b \<longrightarrow> \<alpha> \<bullet> x \<le> \<beta>"
  using assms
  unfolding polyhedron_def valid_ineq_def
  by simp


lemma face_non_empty1:
 fixes A :: "'a :: trivial_conjugatable_linordered_field mat"
 fixes b
 assumes A: "A \<in> carrier_mat nr n"
 assumes b: "b \<in> carrier_vec nr"
  defines "P \<equiv> polyhedron A b"
  assumes "valid_ineq P \<alpha> \<beta>"
  assumes "P \<noteq> {}" 
  shows "Maximum {\<alpha> \<bullet> x | x. x \<in> carrier_vec n \<and> A *\<^sub>v x \<le> b} =
        Minimum {b \<bullet> y | y. y \<ge> 0\<^sub>v nr \<and> A\<^sup>T *\<^sub>v y = \<alpha>}"
    and "has_Maximum {\<alpha> \<bullet> x | x. x \<in> carrier_vec n \<and> A *\<^sub>v x \<le> b}" 
    and "has_Minimum {b \<bullet> y | y. y \<ge> 0\<^sub>v nr \<and> A\<^sup>T *\<^sub>v y = \<alpha>}" 
proof -
  have "\<alpha> \<in> carrier_vec n"  
    using assms(4) valid_ineq_elim(2) by blast
  have sat: "\<exists> x \<in> carrier_vec n. A *\<^sub>v x \<le> b" 
    using assms(3) assms(5) unfolding polyhedron_def by auto
  have bounded: "\<forall> x \<in> carrier_vec n. A *\<^sub>v x \<le> b \<longrightarrow> \<alpha> \<bullet> x \<le> \<beta>" 
    using P_def assms(4) face_primal_bounded by blast
  show "Maximum {\<alpha> \<bullet> x | x. x \<in> carrier_vec n \<and> A *\<^sub>v x \<le> b}
       = Minimum {b \<bullet> y | y. y \<ge> 0\<^sub>v nr \<and> A\<^sup>T *\<^sub>v y = \<alpha>}"
    using strong_duality_theorem_primal_sat_bounded_min_max[of A nr n b \<alpha> \<beta>]
    using A \<open>\<alpha> \<in> carrier_vec n\<close> \<open>b \<in> carrier_vec nr\<close> bounded sat by blast
  show "has_Maximum {\<alpha> \<bullet> x | x. x \<in> carrier_vec n \<and> A *\<^sub>v x \<le> b}"
    using strong_duality_theorem_primal_sat_bounded_min_max[of A nr n b \<alpha> \<beta>]
    using A \<open>\<alpha> \<in> carrier_vec n\<close> \<open>b \<in> carrier_vec nr\<close> bounded sat by blast
  show "has_Minimum {b \<bullet> y | y. y \<ge> 0\<^sub>v nr \<and> A\<^sup>T *\<^sub>v y = \<alpha>}"
   using strong_duality_theorem_primal_sat_bounded_min_max[of A nr n b \<alpha> \<beta>]
    using A \<open>\<alpha> \<in> carrier_vec n\<close> \<open>b \<in> carrier_vec nr\<close> bounded sat by blast
qed


lemma asas:
  fixes a b :: "'a ::  trivial_conjugatable_linordered_field"
  assumes "a \<ge> 0"
  assumes "b \<ge> 0"
  assumes "a +b =0"
  shows "a = 0 \<and> b = 0" 
  using add_nonneg_eq_0_iff assms(1) assms(2) assms(3) by blast

lemma wef:
  fixes f :: "nat \<Rightarrow> 'a :: trivial_conjugatable_linordered_field"
  assumes "(\<Sum>i = 0..<nr. f i) = 0"
  assumes "\<forall> i < nr. f i \<ge> 0"
  shows "\<forall> i < nr. f i = 0" 
  using assms(1-2)
proof(induct rule: nat_induct)
  case 0
  then show ?case by auto
next
  case (Suc n)
  have "\<forall>i<n. 0 \<le> f i" 
    using Suc.prems(2) by force
  then have "(\<Sum>i = 0..<n. f i) \<ge> 0" 
    by (meson atLeastLessThan_iff sum_nonneg)
  have "(\<Sum>i = 0..<(Suc n). f i) = (\<Sum>i = 0..<n. f i) + f n" 
    by simp
  have "f n \<ge> 0" 
    by (simp add: Suc.prems(2))
  then have "f n = 0" using asas 
    using Suc(2) \<open>0 \<le> sum f {0..<n}\<close> \<open>sum f {0..<Suc n} = sum f {0..<n} + f n\<close> by presburger
  then show "\<forall>i<Suc n. f i = 0" 
    by (metis Suc(2) Suc.hyps \<open>0 \<le> f n\<close> \<open>0 \<le> sum f {0..<n}\<close> \<open>\<forall>i<n. 0 \<le> f i\<close> \<open>sum f {0..<Suc n} = sum f {0..<n} + f n\<close> asas less_Suc_eq)
qed
 

lemma complementary_slackness:
 fixes A :: "'a :: trivial_conjugatable_linordered_field mat"
 fixes b
 assumes A: "A \<in> carrier_mat nr n"
 assumes b: "b \<in> carrier_vec nr"
  defines "P \<equiv> polyhedron A b"
  assumes "P \<noteq> {}" 
  assumes "x \<in> carrier_vec n \<and> A *\<^sub>v x \<le> b \<and> \<alpha> \<bullet> x = \<beta>"
  assumes "y \<ge> 0\<^sub>v nr \<and> A\<^sup>T *\<^sub>v y = \<alpha> \<and> b \<bullet> y = \<beta>" 
  shows "\<forall> i < nr. y $ i = 0 \<or> (row A i) \<bullet> x = b $ i"
proof(rule)
      have "\<alpha> \<bullet> x = b \<bullet> y" using assms(5-6)  
        by presburger 
      have " (A\<^sup>T *\<^sub>v y) \<bullet> x = \<alpha> \<bullet> x" 
        by (simp add: assms(6))
      have "y \<in> carrier_vec  nr" using assms(6)
              using Matrix.less_eq_vec_def 
  by (metis carrier_vec_dim_vec index_zero_vec(2)) 
  then   have "(A\<^sup>T *\<^sub>v y) \<bullet> x = y \<bullet> (A *\<^sub>v x)" using transpose_vec_mult_scalar[of A nr n x y]  
    using assms(1) assms(5) by simp
  then have " y \<bullet> (A *\<^sub>v x) = y \<bullet> b" 
    by (metis \<open>(A\<^sup>T *\<^sub>v y) \<bullet> x = \<alpha> \<bullet> x\<close> \<open>\<alpha> \<bullet> x = b \<bullet> y\<close> \<open>y \<in> carrier_vec nr\<close> b comm_scalar_prod)
  then have "y \<bullet> b - y \<bullet> (A *\<^sub>v x)  = 0" by auto
  then have "y \<bullet> ( b - (A *\<^sub>v x) ) = 0" 
    by (metis \<open>y \<in> carrier_vec nr\<close> assms(5) b carrier_vecD carrier_vec_dim_vec less_eq_vec_def scalar_prod_minus_distrib)
  have "b  \<ge> A *\<^sub>v x" using assms(5) by auto 
   have "b - A *\<^sub>v x \<ge> 0\<^sub>v nr"
     unfolding less_eq_vec_def
   proof
     show"dim_vec (0\<^sub>v nr) = dim_vec (b - A *\<^sub>v x)" 
       by (metis \<open>A *\<^sub>v x \<le> b\<close> b carrier_vecD index_minus_vec(2) index_zero_vec(2) less_eq_vec_def)
     show "\<forall>i<dim_vec (b - A *\<^sub>v x). 0\<^sub>v nr $ i \<le> (b - A *\<^sub>v x) $ i" 
       using `b  \<ge> A *\<^sub>v x` 
       by (smt (verit, ccfv_SIG) \<open>dim_vec (0\<^sub>v nr) = dim_vec (b - A *\<^sub>v x)\<close> b carrier_vec_dim_vec diff_eq_diff_less index_minus_vec(1) index_minus_vec(2) index_zero_vec(2) lesseq_vecD linorder_le_less_linear minus_zero_vec order_less_imp_not_eq2 order_less_le_trans)
   qed
   have "\<forall> i < nr. y $ i * (b - A *\<^sub>v x) $ i \<ge> 0" 
   proof
     fix i
     show "i < nr \<longrightarrow> y $ i * (b - A *\<^sub>v x) $ i \<ge> 0"
     proof
       assume "i < nr"
       show "y $ i * (b - A *\<^sub>v x) $ i \<ge> 0" 
       proof -
         have "(b - A *\<^sub>v x) $ i \<ge> 0\<^sub>v nr $ i" using `b - A *\<^sub>v x \<ge> 0\<^sub>v nr`
     by (metis \<open>i < nr\<close> index_zero_vec(2) less_eq_vec_def)
   then have "(b - A *\<^sub>v x) $ i \<ge> 0" 
     by (metis \<open>i < nr\<close> index_zero_vec(1))
   then have "y $ i \<ge> 0" using assms(6) 
     by (metis \<open>i < nr\<close> \<open>y \<in> carrier_vec nr\<close> index_zero_vec(1) lesseq_vecD)
   then show ?thesis 
     using \<open>0 \<le> (b - A *\<^sub>v x) $ i\<close> zero_le_mult_iff by blast
 qed
qed
qed
  have "dim_vec (b - A *\<^sub>v x) = nr" 
    by (metis \<open>A *\<^sub>v x \<le> b\<close> b carrier_vecD index_minus_vec(2) less_eq_vec_def)
  then have "(\<Sum>i = 0..<nr. y $ i * (b - A *\<^sub>v x) $ i) = 0"
     using `y \<bullet> ( b - (A *\<^sub>v x) ) = 0`
      unfolding scalar_prod_def by blast
    then have "\<forall> i < nr. y $ i * (b - A *\<^sub>v x) $ i = 0" 
      using `\<forall>i<nr. 0 \<le> y $ i * (b - A *\<^sub>v x) $ i` 
      using wef 
      by blast

  fix i
  show "i < nr \<longrightarrow> y $ i = 0 \<or> row A i \<bullet> x = b $ i"
  proof
    assume "i < nr"
    show "y $ i = 0 \<or> row A i \<bullet> x = b $ i"
    proof -
      have "y $ i * (b - A *\<^sub>v x) $ i = 0" 
        using \<open>\<forall>i<nr. y $ i * (b - A *\<^sub>v x) $ i = 0\<close> \<open>i < nr\<close> by blast
      then have "y $ i = 0 \<or> (b - A *\<^sub>v x) $ i = 0" 
        using mult_eq_0_iff by blast
      have "(b - A *\<^sub>v x) $ i = 0 \<equiv> b $ i - (A *\<^sub>v x) $ i = 0" 
        
        using \<open>dim_vec (b - A *\<^sub>v x) = nr\<close> \<open>i < nr\<close> by force
      then have "b $ i - (A *\<^sub>v x) $ i = 0 \<equiv> b $ i = (A *\<^sub>v x) $ i"
        using r_right_minus_eq by presburger
      have "(A *\<^sub>v x) $ i = row A i \<bullet> x " 
        using A \<open>i < nr\<close> index_mult_mat_vec by blast
      then show "y $ i = 0 \<or> row A i \<bullet> x = b $ i" 
        using \<open>(b - A *\<^sub>v x) $ i = 0 \<equiv> b $ i - (A *\<^sub>v x) $ i = 0\<close> \<open>b $ i - (A *\<^sub>v x) $ i = 0 \<equiv> b $ i = (A *\<^sub>v x) $ i\<close> \<open>y $ i = 0 \<or> (b - A *\<^sub>v x) $ i = 0\<close> by presburger
    qed
  qed
qed

lemma complementary_slackness2:
 fixes A :: "'a :: trivial_conjugatable_linordered_field mat"
 fixes b
 assumes A: "A \<in> carrier_mat nr n"
 assumes b: "b \<in> carrier_vec nr"
  defines "P \<equiv> polyhedron A b"
  assumes "y \<ge> 0\<^sub>v nr \<and> A\<^sup>T *\<^sub>v y = \<alpha> \<and> b \<bullet> y = \<beta>" 
  assumes "\<forall> i < nr. y $ i = 0 \<or> (row A i) \<bullet> x = b $ i"
  assumes "x \<in> P" 
  shows "x \<in> carrier_vec n \<and> A *\<^sub>v x \<le> b \<and> \<alpha> \<bullet> x = \<beta>"
proof 
  show "x \<in> carrier_vec n" 
    using P_def assms(6) gram_schmidt.polyhedron_def by blast
  have "dim_vec (b - A *\<^sub>v x) = nr" 
    using A by force
  have "\<forall> i < nr. y $ i * (b - A *\<^sub>v x) $ i = 0" 
    by (metis A assms(5) carrier_matD(1) dim_mult_mat_vec index_minus_vec(1) index_mult_mat_vec mult_eq_0_iff r_right_minus_eq)
  then have "y \<bullet> ( b - (A *\<^sub>v x) ) = 0" 
    unfolding scalar_prod_def
    using `dim_vec (b - A *\<^sub>v x) = nr` 
    by (meson atLeastLessThan_iff finsum_zero')
  then have " y \<bullet> (A *\<^sub>v x) = y \<bullet> b" 
    by (smt (verit, ccfv_threshold) \<open>dim_vec (b - A *\<^sub>v x) = nr\<close> assms(4) b carrier_vec_dim_vec eq_iff_diff_eq_0 index_minus_vec(2) index_zero_vec(2) less_eq_vec_def scalar_prod_minus_distrib)
  then   have "(A\<^sup>T *\<^sub>v y) \<bullet> x = y \<bullet> (A *\<^sub>v x)"
   using transpose_vec_mult_scalar[of A nr n x y]  
    using assms(1) `x \<in> carrier_vec n` 
    by (metis assms(4) carrier_dim_vec index_zero_vec(2) less_eq_vec_def)
  then have "\<alpha> \<bullet> x = \<beta>" 
    by (metis \<open>y \<bullet> (A *\<^sub>v x) = y \<bullet> b\<close> assms(4) b carrier_vec_dim_vec comm_scalar_prod index_zero_vec(2) less_eq_vec_def)
  show "A *\<^sub>v x \<le> b \<and> \<alpha> \<bullet> x = \<beta>" 
    using P_def \<open>\<alpha> \<bullet> x = \<beta>\<close> assms(6) gram_schmidt.polyhedron_def by blast
qed
  

definition sub_system where
  "sub_system A b I \<equiv> (submatrix A I UNIV,  vec_of_list (nths (list_of_vec b) I))"

lemma sub_system_fst:
  shows "fst (sub_system A b I) = submatrix A I UNIV" 
  unfolding sub_system_def
  by force

lemma sub_system_snd:
  shows "snd (sub_system A b I) = vec_of_list (nths (list_of_vec b) I)" 
  unfolding sub_system_def
  by force

lemma dim_row_subsyst_mat:
  shows "dim_row (fst (sub_system A b I)) = card {i. i < dim_row A \<and> i \<in> I}" 
  using dim_submatrix(1)[of A I UNIV] sub_system_fst by metis

lemma dim_col_subsyst_mat:
  shows "dim_col (fst (sub_system A b I)) = dim_col A" 
  using dim_submatrix(2)[of A I UNIV] sub_system_fst 
  by (metis (no_types, lifting) Collect_cong UNIV_I card_Collect_less_nat)

lemma dim_row_less_card_I:
  assumes "finite I" 
  shows "dim_row (fst (sub_system A b I)) \<le> card I" 
proof -
  have "{i. i < dim_row A \<and> i \<in> I} \<subseteq> I" by auto
  then have "card {i. i < dim_row A \<and> i \<in> I} \<le> card I" 
    using assms card_mono by blast
  then show ?thesis 
  using dim_row_subsyst_mat by metis
qed

lemma dim_subsyst_vec:
  shows "dim_vec (snd (sub_system A b I)) = card {i. i < dim_vec b \<and> i \<in> I}"
proof -
  have "length (list_of_vec b) = dim_vec b" 
    using Matrix.length_list_of_vec  carrier_vecD by blast
  then show ?thesis
  using sub_system_snd length_nths 
  by (metis Matrix.length_list_of_vec list_of_vec_vec_of_list)
qed

lemma dims_subsyst_same:
  assumes "dim_row A = dim_vec b"
  shows "dim_row (fst (sub_system A b I)) = dim_vec (snd (sub_system A b I))" 
  by (metis  assms dim_row_subsyst_mat dim_subsyst_vec) 

lemma carrier_mat_subsyst:
  assumes "dim_row A = dim_vec b"
  shows "(fst (sub_system A b I)) \<in> carrier_mat (dim_row (fst (sub_system A b I))) (dim_col A)" 
  using dim_col_subsyst_mat by blast

lemma nths_list_pick_vec_same:
  shows "vec_of_list (nths (list_of_vec b) I) = 
    vec (card {i. i<dim_vec b \<and> i\<in>I})  (\<lambda> i. b $ (pick I i))"
  by (smt (verit, best) Collect_cong Matrix.dim_vec_of_list Matrix.length_list_of_vec dim_vec eq_vecI index_vec length_nths list_of_vec_index nth_nths vec_of_list_index)

lemma subsyst_b_i:
  assumes "i< dim_vec (snd (sub_system A b I))"  
  shows "(snd(sub_system A b I)) $ i = b $ (pick I i)" 
  using nths_list_pick_vec_same sub_system_snd 
  by (metis (no_types, lifting) assms dim_subsyst_vec index_vec)
    

lemma pick_index_row_in_A:
  fixes A :: "'a :: trivial_conjugatable_linordered_field mat"
  fixes b
 assumes A: "A \<in> carrier_mat nr n"
 assumes b: "b \<in> carrier_vec nr"
 shows "\<forall> j < dim_vec (snd (sub_system A b I)). 
        row (fst (sub_system A b I)) j = row A (pick I j) \<and> (snd (sub_system A b I)) $ j = b $ (pick I j)"
proof(rule)
  fix j
  have "dim_row A = dim_vec b" 
    using A b  by simp
  show " j < dim_vec (snd (sub_system A b I)) \<longrightarrow>
         row (fst (sub_system A b I)) j = row A (pick I j) \<and> snd (sub_system A b I) $ j = b $ (pick I j)"
  proof
    assume "j < dim_vec (snd (sub_system A b I))" 
    then have "j < card {i. i < dim_row A \<and> i \<in> I}" 
      using `dim_row A = dim_vec b`  
      by (metis  dim_subsyst_vec)
    have "row (submatrix A I UNIV) j = row A (pick I j)" 
      using row_submatrix_UNIV[of j A I]  
      using \<open>j < card {i. i < dim_row A \<and> i \<in> I}\<close> by blast


  show "row (fst (sub_system A b I)) j = row A (pick I j) \<and> (snd (sub_system A b I)) $ j = b $ (pick I j)" 
    
    by (metis \<open>j < dim_vec (snd (sub_system A b I))\<close> \<open>row (submatrix A I UNIV) j = row A (pick I j)\<close> sub_system_fst subsyst_b_i)
qed
qed

lemma exist_index_in_A:
  fixes A :: "'a :: trivial_conjugatable_linordered_field mat"
  fixes b
 assumes A: "A \<in> carrier_mat nr n"
 assumes b: "b \<in> carrier_vec nr"
 shows "\<forall> j < dim_vec (snd (sub_system A b I)). 
        \<exists> i < nr. i \<in> I \<and> row (fst (sub_system A b I)) j = row A i \<and> (snd (sub_system A b I)) $ j = b $ i"
proof(rule)
  fix j
  have "dim_row A = dim_vec b" 
    using A b  by simp
  show " j < dim_vec (snd (sub_system A b I)) \<longrightarrow>
         (\<exists>i<nr. i \<in> I \<and> row (fst (sub_system A b I)) j = row A i \<and> snd (sub_system A b I) $ j = b $ i)"
  proof
    assume "j < dim_vec (snd (sub_system A b I))" 
    then have "j < card {i. i < dim_row A \<and> i \<in> I}" 
      using `dim_row A = dim_vec b`  
      by (metis  dim_subsyst_vec)
  
    have "(pick I j) < nr" 
      by (metis  \<open>j < dim_vec (snd (sub_system A b I))\<close> b carrier_vecD gram_schmidt.dim_subsyst_vec pick_le)
    have "(pick I j) \<in> I" 
      apply(cases "finite I") 
       apply (metis (mono_tags, lifting) \<open>dim_row A = dim_vec b\<close> \<open>j < dim_vec (snd (sub_system A b I))\<close> dim_row_less_card_I dims_subsyst_same le_trans linorder_not_le pick_in_set_le)
      using pick_in_set_inf by auto

  then show " \<exists> i < nr. i \<in> I \<and> row (fst (sub_system A b I)) j = row A i \<and> (snd (sub_system A b I)) $ j = b $ i" 
    
    by (meson A \<open>j < dim_vec (snd (sub_system A b I))\<close> \<open>pick I j < nr\<close> b pick_index_row_in_A)
qed
qed

lemma eqwe:
 fixes A :: "'a :: trivial_conjugatable_linordered_field mat"
 fixes b
 assumes A: "A \<in> carrier_mat nr n"
 assumes b: "b \<in> carrier_vec nr"
  defines "P \<equiv> polyhedron A b"
  assumes "valid_ineq P \<alpha> \<beta>"
  assumes "P \<noteq> {}" 
  assumes "y \<ge> 0\<^sub>v nr \<and> A\<^sup>T *\<^sub>v y = \<alpha> \<and> b \<bullet> y = \<beta>"  
  assumes "x \<in> carrier_vec n \<and> A *\<^sub>v x \<le> b \<and> \<alpha> \<bullet> x = \<beta>"
  shows "x \<in> P"
  and " fst (sub_system A b {i. y $ i > 0 \<and> i < nr})  *\<^sub>v x  = snd (sub_system A b {i. y $ i > 0 \<and> i < nr})" 
  (is "?A' *\<^sub>v x = ?b'")
proof -

  have "y \<in> carrier_vec nr" 
    by (metis assms(6) carrier_vec_dim_vec index_zero_vec(2) less_eq_vec_def)
  show "x \<in> P" using assms(7) P_def 
    using gram_schmidt.polyhedron_def by blast
  have "\<forall> i < nr. y $ i = 0 \<or> (row A i) \<bullet> x = b $ i" 
    using A P_def assms(4) assms(5) assms(6) assms(7) b gram_schmidt.complementary_slackness by blast
  then have "\<forall>i \<in> {i. y $ i > 0 \<and> i < nr}. (row A i) \<bullet> x = b $ i" 
    by force
  have "dim_row ?A' = dim_vec ?b'" 
    by (metis (no_types, lifting) A b carrier_matD(1) carrier_vecD dims_subsyst_same)
  moreover  have "\<forall> i < dim_vec ?b'. (row ?A' i) \<bullet> x = ?b' $ i" 
  proof(rule)+
    fix i
    assume "i < dim_vec ?b'" 
    then obtain j where "j < nr \<and> j \<in> {i. y $ i > 0 \<and> i < nr} \<and> row ?A' i = row A j \<and> ?b' $ i = b $ j"
      using exist_index_in_A[of A nr b "{i. y $ i > 0 \<and> i < nr}"]   
      using A  b by blast
    then have " (row A j) \<bullet> x = b $ j" 
      using \<open>\<forall>i\<in>{i. 0 < y $ i \<and> i < nr}. row A i \<bullet> x = b $ i\<close> by blast
    then show "(row ?A' i) \<bullet> x = ?b' $ i" 
      using \<open>j < nr \<and> j \<in> {i. 0 < y $ i \<and> i < nr} \<and> row (fst (sub_system A b {i. 0 < y $ i \<and> i < nr})) i = row A j \<and> snd (sub_system A b {i. 0 < y $ i \<and> i < nr}) $ i = b $ j\<close> by presburger
  qed
  ultimately show "?A' *\<^sub>v x = ?b'" by auto
qed

lemma I_subsys_same_card:
  assumes A: "A \<in> carrier_mat nr n"
  assumes b: "b \<in> carrier_vec nr"
  assumes "I \<subseteq> {0..<nr}"
  shows "dim_row (fst (sub_system A b I)) = card I"
      "dim_vec (snd (sub_system A b I)) = card I"
proof -
  have "{i. i < nr \<and> i \<in> I} = I" using assms(3) by auto 
  then have " card {i. i < dim_row A \<and> i \<in> I} = card I" using A by auto
  then show "dim_row (fst (sub_system A b I)) = card I" using dim_row_subsyst_mat by metis 
  then show "dim_vec (snd (sub_system A b I)) = card I" using b 
    by (simp add: \<open>{i. i < nr \<and> i \<in> I} = I\<close> dim_subsyst_vec)
qed

lemma eqwe2:
 fixes A :: "'a :: trivial_conjugatable_linordered_field mat"
 fixes b
 assumes A: "A \<in> carrier_mat nr n"
 assumes b: "b \<in> carrier_vec nr"
  defines "P \<equiv> polyhedron A b"
  assumes "valid_ineq P \<alpha> \<beta>"
  assumes "P \<noteq> {}" 
  assumes "y \<ge> 0\<^sub>v nr \<and> A\<^sup>T *\<^sub>v y = \<alpha> \<and> b \<bullet> y = \<beta>"  
  assumes " fst (sub_system A b {i. y $ i > 0 \<and> i < nr})  *\<^sub>v x  = snd (sub_system A b {i. y $ i > 0 \<and> i < nr})" 
  (is "?A' *\<^sub>v x = ?b'")
assumes "x \<in> P" 
shows "\<alpha> \<bullet> x = \<beta>" 
proof -
  let ?I = "{i. y $ i > 0 \<and> i < nr}"

  have "\<forall> i < dim_vec ?b'. (row ?A' i) \<bullet> x = ?b' $ i"
    by (metis (no_types, lifting) assms(7) dim_mult_mat_vec index_mult_mat_vec)
  have "\<forall>i \<in> {i. y $ i > 0 \<and> i < nr}. (row A i) \<bullet> x = b $ i" 
  proof
    fix i
    assume "i \<in> ?I"
    then have "pick ?I (card {a\<in>?I. a < i}) = i"
      using pick_card_in_set[of i ?I]  by simp  
    have "{a\<in>?I. a < i} \<subset> ?I" 
      using \<open>i \<in> {i. 0 < y $ i \<and> i < nr}\<close> by blast
    have "?I \<subseteq> {0..<nr}" by auto
    then have "card ?I = dim_vec ?b'" using I_subsys_same_card(2)
      by (metis (full_types) A b)
    have "finite ?I" by simp
    then have "(card {a\<in>?I. a < i}) < dim_vec ?b'" 
        using `{a\<in>?I. a < i} \<subset> ?I` 
        by (smt (verit, best) \<open>card {i. 0 < y $ i \<and> i < nr} = dim_vec (snd (sub_system A b {i. 0 < y $ i \<and> i < nr}))\<close> psubset_card_mono)

      have "\<exists> j < dim_vec ?b'. pick ?I j  = i"
        
        using \<open>card {a \<in> {i. 0 < y $ i \<and> i < nr}. a < i} < dim_vec (snd (sub_system A b {i. 0 < y $ i \<and> i < nr}))\<close> \<open>pick {i. 0 < y $ i \<and> i < nr} (card {a \<in> {i. 0 < y $ i \<and> i < nr}. a < i}) = i\<close> by blast
      then obtain j where "j < dim_vec ?b'\<and> pick ?I j  = i" by auto
      then have "row A i = row ?A' j" 
        by (metis (no_types, lifting) A b gram_schmidt.pick_index_row_in_A)
      have "b $ i = ?b' $ j" 
        by (simp add: \<open>j < dim_vec (snd (sub_system A b {i. 0 < y $ i \<and> i < nr})) \<and> pick {i. 0 < y $ i \<and> i < nr} j = i\<close> subsyst_b_i)
      then show "(row A i) \<bullet> x = b $ i" 
        using \<open>\<forall>i<dim_vec (snd (sub_system A b {i. 0 < y $ i \<and> i < nr})). row (fst (sub_system A b {i. 0 < y $ i \<and> i < nr})) i \<bullet> x = snd (sub_system A b {i. 0 < y $ i \<and> i < nr}) $ i\<close> \<open>j < dim_vec (snd (sub_system A b {i. 0 < y $ i \<and> i < nr})) \<and> pick {i. 0 < y $ i \<and> i < nr} j = i\<close> \<open>row A i = row (fst (sub_system A b {i. 0 < y $ i \<and> i < nr})) j\<close> by presburger
    qed
    then have "\<forall> i < nr. y $ i = 0 \<or> (row A i) \<bullet> x = b $ i"  
      by (smt (verit, ccfv_SIG) assms(6) index_zero_vec(1) index_zero_vec(2) less_eq_vec_def mem_Collect_eq not_less_iff_gr_or_eq not_less_real)
    then show "\<alpha> \<bullet> x = \<beta>"
      
      using A P_def assms(6) assms(8) b complementary_slackness2 by blast
  qed

lemma char_face1:
 fixes A :: "'a :: trivial_conjugatable_linordered_field mat"
 fixes b
 assumes A: "A \<in> carrier_mat nr n"
 assumes b: "b \<in> carrier_vec nr"
 defines "P \<equiv> polyhedron A b"
 assumes "face P F"
 obtains A' b' I where "((A', b') = sub_system A b I)" "F = {x. A' *\<^sub>v x = b' \<and> x \<in> P}"
proof -
  obtain \<alpha> \<beta> where face:" F = P \<inter> {x |x. \<alpha> \<bullet> x = \<beta>} \<and> valid_ineq P \<alpha> \<beta> \<and> F \<noteq> {}" 
    using assms(4) face_elim2 by presburger
  then have "F = {x. \<alpha> \<bullet> x = \<beta>  \<and> x \<in> P}" by auto
  then have "\<beta> =  Maximum {\<alpha> \<bullet> x | x. x \<in> carrier_vec n \<and> A *\<^sub>v x \<le> b}"
    using face_is_Max'[of F \<alpha> \<beta> A b] face P_def by auto  
  have "has_Maximum {\<alpha> \<bullet> x | x. x \<in> carrier_vec n \<and> A *\<^sub>v x \<le> b}"
    using face_is_Max'[of F \<alpha> \<beta> A b] face P_def by auto
  
  have " \<beta> =  Minimum {b \<bullet> y | y. y \<ge> 0\<^sub>v nr \<and> A\<^sup>T *\<^sub>v y = \<alpha>}"
    using face_non_empty1[of A nr b \<alpha>]  
    by (metis A P_def \<open>\<beta> = Maximum {\<alpha> \<bullet> x |x. x \<in> carrier_vec n \<and> A *\<^sub>v x \<le> b}\<close> assms(4) b face gram_schmidt.face_def)
  have "has_Minimum {b \<bullet> y | y. y \<ge> 0\<^sub>v nr \<and> A\<^sup>T *\<^sub>v y = \<alpha>}" 
    using face_non_empty1[of A nr b \<alpha>]  
    by (metis A P_def assms(4) b face gram_schmidt.face_def)
  then obtain y' where "y' \<ge> 0\<^sub>v nr \<and> A\<^sup>T *\<^sub>v y' = \<alpha> \<and> b \<bullet> y' = \<beta>" 
    using \<open>\<beta> = Minimum {b \<bullet> y |y. 0\<^sub>v nr \<le> y \<and> A\<^sup>T *\<^sub>v y = \<alpha>}\<close> has_MinimumD(1) by fastforce

  let ?A' = "fst (sub_system A b {i. y' $ i > 0 \<and> i < nr})" 
  let ?b' = "snd (sub_system A b {i. y' $ i > 0 \<and> i < nr})"
  have "F = {x. ?A' *\<^sub>v x = ?b' \<and> x \<in> P}" 
  proof(safe)
    {
      fix x
      assume "x \<in> F" 
      then have "x \<in> carrier_vec n \<and> A *\<^sub>v x \<le> b \<and> \<alpha> \<bullet> x = \<beta>" 
        using P_def \<open>F = {x. \<alpha> \<bullet> x = \<beta> \<and> x \<in> P}\<close> gram_schmidt.polyhedron_def by blast
      then show "?A'  *\<^sub>v x  =?b'"
        using eqwe[of A nr b \<alpha> \<beta> y' x] 
        by (metis A P_def \<open>0\<^sub>v nr \<le> y' \<and> A\<^sup>T *\<^sub>v y' = \<alpha> \<and> b \<bullet> y' = \<beta>\<close> assms(4) b face gram_schmidt.face_elim(1))

        
    }
    show "\<And>x. x \<in> F \<Longrightarrow> x \<in> P" 
      using face by fastforce
    {
      fix x
      assume "?A' *\<^sub>v x = ?b'" 
      assume "x \<in> P" 
      show "x \<in> F" using eqwe2[of A nr b \<alpha> \<beta> y' x] 
        using A P_def \<open>0\<^sub>v nr \<le> y' \<and> A\<^sup>T *\<^sub>v y' = \<alpha> \<and> b \<bullet> y' = \<beta>\<close> \<open>fst (sub_system A b {i. 0 < y' $ i \<and> i < nr}) *\<^sub>v x = snd (sub_system A b {i. 0 < y' $ i \<and> i < nr})\<close> \<open>x \<in> P\<close> b face by blast
    }
  qed
  have "((?A', ?b') = sub_system A b {i. 0 < y' $ i \<and> i < nr})" 
    by simp
  then show ?thesis 
    using \<open>F = {x. ?A' *\<^sub>v x = ?b' \<and> x \<in> P}\<close> that by blast
qed

lemma subsyst_valid:
   fixes A :: "'a :: trivial_conjugatable_linordered_field mat"
 fixes b
 assumes A: "A \<in> carrier_mat nr n"
 assumes b: "b \<in> carrier_vec nr"
 assumes "x \<in> polyhedron A b" 
 shows "fst (sub_system A b I) *\<^sub>v x \<le> snd (sub_system A b I)"  
  by (smt (verit, del_insts) A assms(3) b carrier_matD(1) dim_mult_mat_vec dims_subsyst_same gram_schmidt.exist_index_in_A gram_schmidt.polyhedron_def index_mult_mat_vec less_eq_vec_def mem_Collect_eq)



lemma char_face2:
 fixes A :: "'a :: trivial_conjugatable_linordered_field mat"
 fixes b
 assumes A: "A \<in> carrier_mat nr n"
 assumes b: "b \<in> carrier_vec nr"
 defines "P \<equiv> polyhedron A b"
 assumes "((A', b') = sub_system A b I)" 
 assumes "F = {x. A' *\<^sub>v x = b' \<and> x \<in> P}"
 assumes "F \<noteq> {}" 
 shows  "face P F"
proof -
  let ?\<alpha> = "A'\<^sup>T *\<^sub>v 1\<^sub>v (dim_vec b')"
  let ?\<beta> = " 1\<^sub>v (dim_vec b') \<bullet> b'"
  have "?\<beta> = sum (\<lambda> i. b' $ i) {0..<dim_vec b'}"   
    by auto


  have "{x. A' *\<^sub>v x = b' \<and> x \<in> P} = {x. ?\<alpha> \<bullet> x = ?\<beta> \<and> x \<in> P}"
  proof(safe)
    {
      fix x
      assume "x \<in> P" 
      assume " b' = A' *\<^sub>v x"
      have "A' \<in> carrier_mat (dim_vec b') n" using carrier_mat_subsyst 
        by (metis A \<open>b' = A' *\<^sub>v x\<close> assms(4) b carrier_matD(1) carrier_matD(2) carrier_vecD dim_mult_mat_vec fst_conv)
      have "x \<in> carrier_vec n" using `x \<in> P` P_def 
        using gram_schmidt.polyhedron_def by blast
      have "(A'\<^sup>T *\<^sub>v 1\<^sub>v (dim_vec b')) \<bullet> x =  1\<^sub>v (dim_vec b') \<bullet> (A' *\<^sub>v x)"
        using transpose_vec_mult_scalar[of A' "dim_vec b'" n  x "1\<^sub>v (dim_vec b')"]
        using `A' \<in> carrier_mat (dim_vec b') n` `x \<in> carrier_vec n` by simp
      then show "(A'\<^sup>T *\<^sub>v 1\<^sub>v (dim_vec (A' *\<^sub>v x))) \<bullet> x =
         1\<^sub>v (dim_vec (A' *\<^sub>v x)) \<bullet> (A' *\<^sub>v x)" 
        using \<open>b' = A' *\<^sub>v x\<close> by blast
    }
    fix x
    assume "(A'\<^sup>T *\<^sub>v 1\<^sub>v (dim_vec b')) \<bullet> x = 1\<^sub>v (dim_vec b') \<bullet> b'"
    assume " x \<in> P " 
    have "A' \<in> carrier_mat (dim_vec b') n" using carrier_mat_subsyst     
      by (metis A assms(4) b carrier_matD(1) carrier_matD(2) carrier_vecD dims_subsyst_same fst_conv snd_conv)
     have "x \<in> carrier_vec n" using `x \<in> P` P_def 
        using gram_schmidt.polyhedron_def by blast
    have "(A'\<^sup>T *\<^sub>v 1\<^sub>v (dim_vec b')) \<bullet> x =  1\<^sub>v (dim_vec b') \<bullet> (A' *\<^sub>v x)"
        using transpose_vec_mult_scalar[of A' "dim_vec b'" n  x "1\<^sub>v (dim_vec b')"]
        using `A' \<in> carrier_mat (dim_vec b') n` `x \<in> carrier_vec n` by simp
      then have "1\<^sub>v (dim_vec b') \<bullet> (A' *\<^sub>v x) = 1\<^sub>v (dim_vec b') \<bullet> b'" 
        using \<open>(A'\<^sup>T *\<^sub>v 1\<^sub>v (dim_vec b')) \<bullet> x = 1\<^sub>v (dim_vec b') \<bullet> b'\<close> by presburger
      have "(A' *\<^sub>v x) \<le> b'" using `x \<in> P` P_def subsyst_valid[of A nr b x I]  
        by (metis A assms(4) b fst_conv snd_conv)
      then have "\<forall> i < dim_vec b'. (A' *\<^sub>v x) $ i \<le> b' $ i" 
        using less_eq_vec_def by blast
      show "A' *\<^sub>v x = b'" 
      proof(rule ccontr)
        assume "A' *\<^sub>v x \<noteq> b'" 
        then obtain i where "i < dim_vec b'\<and> (A' *\<^sub>v x) $ i \<noteq> b' $ i"
          by (metis \<open>A' *\<^sub>v x \<le> b'\<close> antisym less_eq_vec_def)
        then have "(A' *\<^sub>v x) $ i < b' $ i" 
          using \<open>\<forall>i<dim_vec b'. (A' *\<^sub>v x) $ i \<le> b' $ i\<close> order_le_imp_less_or_eq by blast
        then have "sum (\<lambda> i. (A' *\<^sub>v x) $ i) {0..<dim_vec b'} 
                  < sum (\<lambda> i. b' $ i) {0..<dim_vec b'}"
        by (metis \<open>\<forall>i<dim_vec b'. (A' *\<^sub>v x) $ i \<le> b' $ i\<close> \<open>i < dim_vec b' \<and> (A' *\<^sub>v x) $ i \<noteq> b' $ i\<close> atLeastLessThan_iff finite_atLeastLessThan linorder_le_less_linear not_less_zero sum_strict_mono_ex1)
      then have "1\<^sub>v (dim_vec b') \<bullet> (A' *\<^sub>v x) < 1\<^sub>v (dim_vec b') \<bullet> b'"
        by (metis \<open>A' *\<^sub>v x \<le> b'\<close> carrier_vec_dim_vec less_eq_vec_def scalar_prod_left_one)
        then show False 
          using \<open>1\<^sub>v (dim_vec b') \<bullet> (A' *\<^sub>v x) = 1\<^sub>v (dim_vec b') \<bullet> b'\<close> by linarith
      qed
    qed
    have "valid_ineq P ?\<alpha> ?\<beta>" 
      unfolding valid_ineq_def 
    proof(safe)
      {   fix x
      assume "x \<in> P" 
      
      have "(A' *\<^sub>v x) \<le> b'" using `x \<in> P` P_def subsyst_valid[of A nr b x I]  
        by (metis A assms(4) b fst_conv snd_conv)
    then have "sum (\<lambda> i. (A' *\<^sub>v x) $ i) {0..<dim_vec b'} 
                  \<le> sum (\<lambda> i. b' $ i) {0..<dim_vec b'}" 
      by (meson atLeastLessThan_iff less_eq_vec_def sum_mono)
    then have " 1\<^sub>v (dim_vec b') \<bullet> (A' *\<^sub>v x) \<le>  1\<^sub>v (dim_vec b') \<bullet> b'"
        by (metis \<open>A' *\<^sub>v x \<le> b'\<close> carrier_vec_dim_vec less_eq_vec_def scalar_prod_left_one)
     have "A' \<in> carrier_mat (dim_vec b') n" using carrier_mat_subsyst     
      by (metis A assms(4) b carrier_matD(1) carrier_matD(2) carrier_vecD dims_subsyst_same fst_conv snd_conv)
     have "x \<in> carrier_vec n" using `x \<in> P` P_def 
        using gram_schmidt.polyhedron_def by blast
    have "(A'\<^sup>T *\<^sub>v 1\<^sub>v (dim_vec b')) \<bullet> x =  1\<^sub>v (dim_vec b') \<bullet> (A' *\<^sub>v x)"
        using transpose_vec_mult_scalar[of A' "dim_vec b'" n  x "1\<^sub>v (dim_vec b')"]
        using `A' \<in> carrier_mat (dim_vec b') n` `x \<in> carrier_vec n` by simp
      show "(A'\<^sup>T *\<^sub>v 1\<^sub>v (dim_vec b')) \<bullet> x \<le> 1\<^sub>v (dim_vec b') \<bullet> b'"
        
        using \<open>(A'\<^sup>T *\<^sub>v 1\<^sub>v (dim_vec b')) \<bullet> x = 1\<^sub>v (dim_vec b') \<bullet> (A' *\<^sub>v x)\<close> \<open>1\<^sub>v (dim_vec b') \<bullet> (A' *\<^sub>v x) \<le> 1\<^sub>v (dim_vec b') \<bullet> b'\<close> by presburger
     
    }
    show " A'\<^sup>T *\<^sub>v 1\<^sub>v (dim_vec b') \<in> carrier_vec n"
      
      by (metis A assms(4) b carrier_matD(1) carrier_matD(2) carrier_vecD gram_schmidt.carrier_mat_subsyst gram_schmidt.dims_subsyst_same mult_mat_vec_carrier one_carrier_vec prod.sel(1) prod.sel(2) transpose_carrier_mat)
  qed
  then show "face P F" using face_intro2[of P ?\<alpha> ?\<beta> F] assms(5-6)
        `{x. A' *\<^sub>v x = b' \<and> x \<in> P} = {x. ?\<alpha> \<bullet> x = ?\<beta> \<and> x \<in> P}` by auto 
qed
      

lemma character_faces:
  fixes A b
  defines "P \<equiv> polyhedron A b"
  assumes "F \<subseteq> P"
  shows "face P F \<longleftrightarrow> F \<noteq> {} \<and> (\<exists> A' b'. F = {x. A' *\<^sub>v x = b'  \<and> x \<in> P} \<and> 
        system A' b' \<subseteq> system A' b')" 
  oops

end

end