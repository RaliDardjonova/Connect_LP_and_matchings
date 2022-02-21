theory Faces
  imports  Linear_Inequalities.Decomposition_Theorem 
           Linear_Inequalities.Missing_Matrix
           LP_Duality.LP_Duality
          Jordan_Normal_Form.Matrix
          Jordan_Normal_Form.DL_Rank_Submatrix
          Subsystems

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
  then show "\<beta> = Maximum {\<alpha> \<bullet> x |x. x \<in> P}" 
    by (smt (verit, ccfv_SIG) assms(1) eqMaximumI mem_Collect_eq valid_ineq_elim(1))
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
  have \<beta>_max: "\<beta> = Maximum {\<alpha> \<bullet> x |x. x \<in> P} \<and> has_Maximum {\<alpha> \<bullet> x |x. x \<in> P}" using assms by force 
  then show "\<forall>x\<in>P. \<alpha> \<bullet> x \<le> \<beta>" 
    using has_MaximumD(2) by blast
  have "\<beta> \<in> {\<alpha> \<bullet> x |x. x \<in> P}" 
    using \<beta>_max has_MaximumD(1) by blast
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
  assumes "face P F"
  shows "F \<subseteq> P"
  using assms unfolding face_def 
  by auto

lemma face_is_Max':
  assumes "F = {x. \<alpha> \<bullet> x = \<beta>  \<and> x \<in> P}"
  assumes "valid_ineq P \<alpha> \<beta>"
  assumes "F \<noteq> {}" 
  shows "\<beta> =  Maximum {\<alpha> \<bullet> x | x. x \<in> P}" (is "\<beta> = Maximum ?Ineq")
  and "has_Maximum {\<alpha> \<bullet> x | x. x \<in> P}"  (is "has_Maximum ?Ineq")
proof - 
  have "\<beta> \<in> {\<alpha> \<bullet> x | x. x \<in> P}" using assms(1) assms(3) by auto
  then show "\<beta> = Maximum ?Ineq" 
    by (smt (verit, best) assms(2) eqMaximumI valid_ineq_def mem_Collect_eq)
  show "has_Maximum ?Ineq"
    using \<open>\<beta> \<in> {\<alpha> \<bullet> x |x. x \<in> P}\<close> assms(2) has_Maximum_def valid_ineq_elim(1) by fastforce
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

lemma if_sum_0_then_all_0:
  fixes f :: "nat \<Rightarrow> 'a :: trivial_conjugatable_linordered_field"
  assumes "(\<Sum>i = 0..<nr. f i) = 0"
  assumes "\<forall> i < nr. f i \<ge> 0"
  shows "\<forall> i < nr. f i = 0" 
  using assms(1-2)
  apply (induct rule: nat_induct)
   apply blast
  by (metis add_nonneg_eq_0_iff atLeastLessThan_iff less_Suc_eq 
      sum.atLeast0_lessThan_Suc sum_nonneg)

lemma dsf:
 fixes a :: "'a :: trivial_conjugatable_linordered_field vec"
 assumes "a \<in> carrier_vec nr"
 assumes "b \<in> carrier_vec nr"
  assumes "y \<in> carrier_vec nr"
  assumes "a \<le> b" 
  assumes "y \<bullet> a = y \<bullet> b" 
  assumes "y \<ge> 0\<^sub>v nr" 
  shows "\<forall> i < nr. y $ i * (b - a) $ i = 0" 
proof -
  have "y \<bullet> b - y \<bullet> a  = 0" using assms(5)  by auto
  then have "y \<bullet> (b - a) = 0" 
    by (metis assms(1-3) scalar_prod_minus_distrib)
  then have "(\<Sum>i = 0..<nr. y $ i * (b - a) $ i) = 0"
     unfolding scalar_prod_def
     by (metis assms(1) carrier_vecD index_minus_vec(2))
   have "\<forall> i < nr. y $ i * (b - a) $ i \<ge> 0" 
     by (metis assms(1) assms(2) assms(3) assms(4) assms(6) carrier_vecD diff_ge_0_iff_ge 
         index_minus_vec(1) index_zero_vec(1) lesseq_vecD zero_le_mult_iff)
   then show "\<forall> i < nr. y $ i * (b - a) $ i = 0"  using if_sum_0_then_all_0 
     using \<open>(\<Sum>i = 0..<nr. y $ i * (b - a) $ i) = 0\<close> by blast
 qed

lemma complementary_slackness:
  fixes A :: "'a :: trivial_conjugatable_linordered_field mat"
  assumes A: "A \<in> carrier_mat nr n"
  assumes b: "b \<in> carrier_vec nr"
  assumes "x \<in> carrier_vec n \<and> A *\<^sub>v x \<le> b \<and> \<alpha> \<bullet> x = \<beta>"
  assumes "y \<ge> 0\<^sub>v nr \<and> A\<^sup>T *\<^sub>v y = \<alpha> \<and> b \<bullet> y = \<beta>" 
  shows "\<forall> i < nr. y $ i = 0 \<or> (row A i) \<bullet> x = b $ i"
proof -
  have "dim_row A = nr" using A by auto
  have "y \<in> carrier_vec nr" 
    by (metis assms(4) carrier_dim_vec index_zero_vec(2) less_eq_vec_def)
  then   have "(A\<^sup>T *\<^sub>v y) \<bullet> x = y \<bullet> (A *\<^sub>v x)" using transpose_vec_mult_scalar[of A nr n x y]  
    using assms(1) assms(3) by simp
  then have " y \<bullet> (A *\<^sub>v x) = y \<bullet> b" 
    by (metis \<open>y \<in> carrier_vec nr\<close> assms(3) assms(4) b comm_scalar_prod)
  then have "\<forall> i < nr. y $ i * (b - A *\<^sub>v x) $ i = 0" using dsf[of "A *\<^sub>v x" nr b y]  
    using A \<open>y \<in> carrier_vec nr\<close> assms(3) assms(4) b mult_mat_vec_carrier by blast
  then show ?thesis 
    by (metis \<open>dim_row A = nr\<close> dim_mult_mat_vec index_minus_vec(1) index_mult_mat_vec
        no_zero_divisors r_right_minus_eq)
qed

lemma complementary_slackness2':
 fixes A :: "'a :: trivial_conjugatable_linordered_field mat"
 assumes A: "A \<in> carrier_mat nr n"
 assumes b: "b \<in> carrier_vec nr"
  assumes "y \<ge> 0\<^sub>v nr \<and> A\<^sup>T *\<^sub>v y = \<alpha> \<and> b \<bullet> y = \<beta>" 
  assumes "\<forall> i < nr. y $ i = 0 \<or> (row A i) \<bullet> x = b $ i"
  assumes "x \<in> polyhedron A b"
  shows "\<alpha> \<bullet> x = \<beta>"
proof -
  have "y \<in> carrier_vec nr" 
    by (metis assms(3) carrier_dim_vec index_zero_vec(2) less_eq_vec_def)
  have "A *\<^sub>v x \<in> carrier_vec nr"  
    by (metis A carrier_dim_vec carrier_matD(1) dim_mult_mat_vec)
  have "dim_vec (b - A *\<^sub>v x) = nr" 
    using A by force
  then have "\<forall> i < nr. y $ i * (b - A *\<^sub>v x) $ i = 0" 
    using assms(4) index_minus_vec(2) by auto
  then have "y \<bullet> (b - (A *\<^sub>v x)) = 0" 
    by (metis (no_types, lifting) \<open>dim_vec (b - A *\<^sub>v x) = nr\<close>
        atLeastLessThan_iff finsum_zero' scalar_prod_def)
  then have " y \<bullet> (A *\<^sub>v x) = y \<bullet> b" 
    using scalar_prod_minus_distrib right_minus_eq
    by (metis \<open>y \<in> carrier_vec nr\<close> \<open>A *\<^sub>v x \<in> carrier_vec nr\<close> b)
  then   have "(A\<^sup>T *\<^sub>v y) \<bullet> x = y \<bullet> (A *\<^sub>v x)"
   using transpose_vec_mult_scalar[of A nr n x y]  
   using A \<open>y \<in> carrier_vec nr\<close> assms(5) polyhedron_def by blast
  then show "\<alpha> \<bullet> x = \<beta>" 
    using \<open>y \<bullet> (A *\<^sub>v x) = y \<bullet> b\<close> \<open>y \<in> carrier_vec nr\<close> assms(3) b comm_scalar_prod by auto
qed

lemma eqwe:
 fixes A :: "'a :: trivial_conjugatable_linordered_field mat"
 assumes A: "A \<in> carrier_mat nr n"
 assumes b: "b \<in> carrier_vec nr"
  assumes "y \<ge> 0\<^sub>v nr \<and> A\<^sup>T *\<^sub>v y = \<alpha> \<and> b \<bullet> y = \<beta>"  
  assumes "x \<in> carrier_vec n \<and> A *\<^sub>v x \<le> b \<and> \<alpha> \<bullet> x = \<beta>"
  shows "fst (sub_system A b {i. y $ i > 0 \<and> i < nr}) *\<^sub>v x = snd (sub_system A b {i. y $ i > 0 \<and> i < nr})" 
  (is "?A' *\<^sub>v x = ?b'")
proof -
  have "dim_row A = dim_vec b"
      using A  b by auto
  have "\<forall> i < nr. y $ i = 0 \<or> (row A i) \<bullet> x = b $ i" 
    using assms complementary_slackness by blast
  then have "\<forall>i \<in> {i. y $ i > 0 \<and> i < nr} \<inter> {0..<dim_row A}. (row A i) \<bullet> x = b $ i" 
    by fastforce
  then have "\<forall> i < dim_row ?A'. (row ?A' i) \<bullet> x = ?b' $ i" 
    using subsystem_fulfills_P'[of A b ?A' ?b' _ "(\<lambda> a c. a \<bullet> x = c)"] 
    using \<open>dim_row A = dim_vec b\<close> prod.collapse by blast
  then show "?A' *\<^sub>v x = ?b'" 
    by (meson \<open>dim_row A = dim_vec b\<close> dims_subsyst_same eq_for_all_index_then_eq)
qed

lemma eqwe2:
  fixes A :: "'a :: trivial_conjugatable_linordered_field mat"
  assumes A: "A \<in> carrier_mat nr n"
  assumes b: "b \<in> carrier_vec nr"
  assumes "y \<ge> 0\<^sub>v nr \<and> A\<^sup>T *\<^sub>v y = \<alpha> \<and> b \<bullet> y = \<beta>"  
  assumes " fst (sub_system A b {i. y $ i > 0 \<and> i < nr})  *\<^sub>v x  = snd (sub_system A b {i. y $ i > 0 \<and> i < nr})" 
    (is "?A' *\<^sub>v x = ?b'")
  assumes "x \<in> polyhedron A b" 
  shows "\<alpha> \<bullet> x = \<beta>" 
proof -
  have "dim_vec y = nr" 
    by (metis assms(3) index_zero_vec(2) less_eq_vec_def)
  have "dim_row A = dim_vec b" using A b by auto
  then have "\<forall>i \<in> {i. y $ i > 0 \<and> i < nr} \<inter> {0..<dim_row A}. (row A i) \<bullet> x = b $ i"
    using subsystem_fulfills_P[of A b ?A' ?b' _ "(\<lambda> a c. a \<bullet> x = c)"] 
    by (metis (no_types, lifting) \<open>dim_row A = dim_vec b\<close> assms(4) index_mult_mat_vec prod.collapse)
  then have "\<forall>i \<in> {i. y $ i > 0 \<and> i < nr}. (row A i) \<bullet> x = b $ i" using A by auto
  then have "\<forall> i < nr. y $ i = 0 \<or> (row A i) \<bullet> x = b $ i"  
    by (metis (no_types, lifting) \<open>dim_vec y = nr\<close> assms(3) index_zero_vec(1) less_eq_vec_def
        mem_Collect_eq order_le_imp_less_or_eq)
  then show "\<alpha> \<bullet> x = \<beta>"    
    using A  assms(3) assms(5) b complementary_slackness2' by blast 
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
    using face_is_Max'(1)[of F \<alpha> \<beta> P] face P_def 
    by (smt (verit, best) Collect_cong mem_Collect_eq polyhedron_def)  
  have "has_Maximum {\<alpha> \<bullet> x | x. x \<in> carrier_vec n \<and> A *\<^sub>v x \<le> b}"
    using face_is_Max'(2)[of F \<alpha> \<beta> P] face P_def 
    by (metis (mono_tags, lifting) A  assms(4) b gram_schmidt.face_def gram_schmidt.face_non_empty1(2))
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
        using eqwe[of A nr b y' \<alpha> \<beta> x ] 
        by (metis A  \<open>0\<^sub>v nr \<le> y' \<and> A\<^sup>T *\<^sub>v y' = \<alpha> \<and> b \<bullet> y' = \<beta>\<close>  b)

        
    }
    show "\<And>x. x \<in> F \<Longrightarrow> x \<in> P" 
      using face by fastforce
    {
      fix x
      assume "?A' *\<^sub>v x = ?b'" 
      assume "x \<in> P" 
      show "x \<in> F" using eqwe2[of A nr b y' \<alpha> \<beta> x] 
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
  by (smt (verit, del_insts) A assms(3) b carrier_matD(1) dim_mult_mat_vec dims_subsyst_same exist_index_in_A gram_schmidt.polyhedron_def index_mult_mat_vec less_eq_vec_def mem_Collect_eq)



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
      
      by (metis A assms(4) b carrier_matD(1) carrier_matD(2) carrier_vecD carrier_mat_subsyst dims_subsyst_same mult_mat_vec_carrier one_carrier_vec prod.sel(1) prod.sel(2) transpose_carrier_mat)
  qed
  then show "face P F" using face_intro2[of P ?\<alpha> ?\<beta> F] assms(5-6)
        `{x. A' *\<^sub>v x = b' \<and> x \<in> P} = {x. ?\<alpha> \<bullet> x = ?\<beta> \<and> x \<in> P}` by auto 
qed
      

lemma exist_max_subsystem:
  fixes A :: "'a :: trivial_conjugatable_linordered_field mat"
 fixes b
 assumes A: "A \<in> carrier_mat nr n"
 assumes b: "b \<in> carrier_vec nr"
 defines "P \<equiv> polyhedron A b"
 assumes "face P F"
 obtains A' b' I  where "((A', b') = sub_system A b I)" 
                      "F = {x. A' *\<^sub>v x = b' \<and> x \<in> P}"
                      "dim_vec b' = Max {dim_vec d| C d I.  (C, d) = sub_system A b I \<and> F = {x. C *\<^sub>v x = d \<and> x \<in> P}}"
proof-
  have "dim_vec b = nr" using b by auto
  let ?M = "{dim_vec d| C d I.  (C, d) = sub_system A b I \<and> F = {x. C *\<^sub>v x = d \<and> x \<in> P}}"
  have "?M \<noteq> {}" using char_face1[of A nr b F] assms
    by (smt (verit, best) Collect_cong Collect_empty_eq)
  have "\<forall> nd \<in> ?M. nd\<le> nr"  
    by (smt (verit, ccfv_SIG) \<open>dim_vec b = nr\<close> dim_subsyst_vec_less_b mem_Collect_eq snd_eqD)
  then have "?M \<subseteq> {0..<nr+1}" by fastforce 
  then have "finite ?M" 
    using subset_eq_atLeast0_lessThan_finite by blast
  then have "Max ?M \<in> ?M \<and> (\<forall>a \<in> ?M. a \<le> (Max ?M))"
    using eq_Max_iff[of ?M] `?M \<noteq> {}`
    by auto
  then obtain C d I  where  "(C, d) = sub_system A b I \<and> F = {x. C *\<^sub>v x = d \<and> x \<in> P} \<and> dim_vec d = Max ?M"
    by auto
  then show ?thesis by (smt (z3) \<open>\<And>thesis. (\<And>C d I. (C, d) = sub_system A b I \<and> F = {x. C *\<^sub>v x = d \<and> x \<in> P} \<and> dim_vec d = Max {uu. \<exists>C d I. uu = dim_vec d \<and> (C, d) = sub_system A b I \<and> F = {x. C *\<^sub>v x = d \<and> x \<in> P}} \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> that) 
qed

lemma exist_min_ineq_subsystem:
  fixes A :: "'a :: trivial_conjugatable_linordered_field mat"
 fixes b
 assumes A: "A \<in> carrier_mat nr n"
 assumes b: "b \<in> carrier_vec nr"
 defines "P \<equiv> polyhedron A b"
 assumes "((A', b') = sub_system A b I')"
 assumes "F = {x. A' *\<^sub>v x = b' \<and> x \<in> P}"
 obtains A'' b'' I''
 where  "((A'', b'') = sub_system A b I'')"
       "F = {x. x \<in> carrier_vec n \<and> A' *\<^sub>v x = b' \<and> A'' *\<^sub>v x \<le> b'' }"
       "dim_vec b'' = Min {dim_vec d| C d I.  (C, d) = sub_system A b I 
                                  \<and> F = {x. x \<in> carrier_vec n \<and> A' *\<^sub>v x = b' \<and> C *\<^sub>v x \<le> d}}"
proof -
   have "dim_vec b = nr" using b by auto
   let ?M = "{dim_vec d| C d I.  (C, d) = sub_system A b I \<and> F = {x. x \<in> carrier_vec n \<and> A' *\<^sub>v x = b' \<and> C *\<^sub>v x \<le> d}}"
   have "(A, b) = sub_system A b UNIV" using itself_is_subsyst by auto
   have "F = {x. x \<in> carrier_vec n \<and>  A' *\<^sub>v x = b' \<and> A *\<^sub>v x \<le> b}" 
    using assms(5) P_def  unfolding polyhedron_def 
    by blast
  then have "(A, b) = sub_system A b UNIV \<and> F = {x. x \<in> carrier_vec n \<and> A' *\<^sub>v x = b' \<and> A *\<^sub>v x \<le> b}"
     using itself_is_subsyst by blast

   then have "dim_vec b \<in> ?M" by auto
   then  have "?M \<noteq> {}" by auto
  have "\<forall> nd \<in> ?M. nd\<le> nr"  
    by (smt (verit, ccfv_SIG) \<open>dim_vec b = nr\<close> dim_subsyst_vec_less_b mem_Collect_eq snd_eqD)
  then have "?M \<subseteq> {0..<nr+1}" by fastforce 
  then have "finite ?M" 
    using subset_eq_atLeast0_lessThan_finite by blast
  then have "Min ?M \<in> ?M \<and> (\<forall>a \<in> ?M. a \<ge> (Min ?M))"
    using eq_Min_iff[of ?M] `?M \<noteq> {}`
    by auto
  then obtain C d I  where  C_d:"(C, d) = sub_system A b I \<and>
                                  F = {x. x \<in> carrier_vec n \<and> A' *\<^sub>v x = b' \<and> C *\<^sub>v x \<le> d }
                                   \<and> dim_vec d = Min ?M"
    by auto
  then show ?thesis 
    by (smt (z3) \<open>\<And>thesis. (\<And>C d I. (C, d) = sub_system A b I \<and> F = {x \<in> carrier_vec n. A' *\<^sub>v x = b' \<and> C *\<^sub>v x \<le> d} \<and> dim_vec d = Min {uu. \<exists>C d I. uu = dim_vec d \<and> (C, d) = sub_system A b I \<and> F = {x \<in> carrier_vec n. A' *\<^sub>v x = b' \<and> C *\<^sub>v x \<le> d}} \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> that)    
qed

text \<open>Minimal Faces\<close>

text \<open>Minimal faces are faces that doesn't contain any other face. They are affine spaces\<close>

definition min_face where
  "min_face P F \<equiv> face P F \<and> (\<nexists> F'. F' \<subset> F \<and> face P F')"

lemma min_face_elim[elim]:
  assumes "min_face P F" 
  shows "face P F" 
       "(\<nexists> F'. F' \<subset> F \<and> face P F')"
  using assms unfolding min_face_def by auto

lemma min_face_intro[intro]:
  assumes "face P F"
  assumes "(\<nexists> F'. F' \<subset> F \<and> face P F')"
  shows "min_face P F"
  unfolding min_face_def using assms by auto


thm "pick_index_row_in_A" 


     
 

lemma smult_minus_distrib_vec:
  assumes "v \<in> carrier_vec n" "w \<in> carrier_vec n"
  shows "(a::'b::ring) \<cdot>\<^sub>v (v - w) = a \<cdot>\<^sub>v v - a \<cdot>\<^sub>v w"
  apply (rule eq_vecI)
  unfolding smult_vec_def minus_vec_def
  
  using assms(1) assms(2) right_diff_distrib 
   apply force
  by force

lemma dasdasd:
  assumes "v \<in> carrier_vec n" "w \<in> carrier_vec n"
  shows "v + (a::'b::ring) \<cdot>\<^sub>v w - a  \<cdot>\<^sub>v v = v  - a \<cdot>\<^sub>v v + a  \<cdot>\<^sub>v w" 
  using assms(1) assms(2) by auto

lemma char_min_face1:
  fixes A :: "'a :: trivial_conjugatable_linordered_field mat"
 fixes b
 assumes A: "A \<in> carrier_mat nr n"
 assumes b: "b \<in> carrier_vec nr"
 defines "P \<equiv> polyhedron A b"
 assumes "min_face P F"
 obtains A' b' I where  " F = {x. x \<in> carrier_vec n \<and> A' *\<^sub>v x = b'}" "(A', b') = sub_system A b I" 
proof -
  have "dim_vec b = nr" using b by auto
  let ?M = "{dim_vec d| C d I.  (C, d) = sub_system A b I \<and> F = {x. C *\<^sub>v x = d \<and> x \<in> P}}"
  
  have "\<forall> nd \<in> ?M. nd\<le> nr"  
    by (smt (verit, ccfv_SIG) \<open>dim_vec b = nr\<close> dim_subsyst_vec_less_b mem_Collect_eq snd_eqD)
  then have "?M \<subseteq> {0..<nr+1}" by fastforce 
  then have 1:"finite ?M"  
    using subset_eq_atLeast0_lessThan_finite by blast
  have "face P F" using assms(4) min_face_elim by simp
  then obtain A' b' I  where sub_A:"((A', b') = sub_system A b I)" 
                      "F = {x. A' *\<^sub>v x = b' \<and> x \<in> P}"
                      "dim_vec b' = Max {dim_vec d| C d I.  (C, d) = sub_system A b I \<and> F = {x. C *\<^sub>v x = d \<and> x \<in> P}}"

    using exist_max_subsystem[of A nr b F] assms(1-3) 
    by auto

  then obtain A'' b'' I''
    where  "((A'', b'') = sub_system A b I'')"
       "F = {x. x \<in> carrier_vec n \<and> A' *\<^sub>v x = b' \<and> A'' *\<^sub>v x \<le> b'' }"
       "dim_vec b'' = Min {dim_vec d| C d I.  (C, d) = sub_system A b I 
                                  \<and> F = {x. x \<in> carrier_vec n \<and> A' *\<^sub>v x = b' \<and> C *\<^sub>v x \<le> d}}"
    using  exist_min_ineq_subsystem[of A nr b A' b' I F] assms(1-3) by auto

  let ?N =  "{dim_vec d| C d I.  (C, d) = sub_system A b I 
                                  \<and> F = {x. x \<in> carrier_vec n \<and> A' *\<^sub>v x = b' \<and> C *\<^sub>v x \<le> d}}" 

 have "dim_vec b = nr" using b by auto

  have "\<forall> nd \<in> ?N. nd\<le> nr"  
    by (smt (verit, ccfv_SIG) \<open>dim_vec b = nr\<close> dim_subsyst_vec_less_b mem_Collect_eq snd_eqD)
  then have "?N \<subseteq> {0..<nr+1}" by fastforce 
  then have 2:"finite ?N"  
    using subset_eq_atLeast0_lessThan_finite by blast
  have "I \<inter> I'' \<inter> {0..<nr}= {}"
  proof(rule ccontr)
    assume "I \<inter> I'' \<inter> {0..<nr}\<noteq> {}" 
    then obtain i where i:"i \<in> I \<and> i \<in> I'' \<and> i < nr" by fastforce
    then obtain C d where "(C, d) = sub_system A b (I'' - {i})" 
      by (metis surj_pair)
    
    then have "{x. A'' *\<^sub>v x \<le> b''} = {x. C *\<^sub>v x \<le> d \<and> row A i \<bullet> x \<le> b $ i}"
      using remove_index_sub_system[of A b i I'' A'' b'' C d] 
      using \<open>(A'', b'') = sub_system A b I''\<close> i 
      using A \<open>dim_vec b = nr\<close> by blast
    moreover have "{x. x \<in> carrier_vec n \<and> A' *\<^sub>v x = b' \<and> A'' *\<^sub>v x \<le> b'' } =
            {x. x \<in> carrier_vec n \<and> A' *\<^sub>v x = b'} \<inter> {x.  A'' *\<^sub>v x \<le> b''}" by auto
    moreover have "{x. x \<in> carrier_vec n \<and> A' *\<^sub>v x = b' \<and> C *\<^sub>v x \<le> d \<and> row A i \<bullet> x \<le> b $ i} =
            {x. x \<in> carrier_vec n \<and> A' *\<^sub>v x = b'} \<inter> {x. C *\<^sub>v x \<le> d \<and> row A i \<bullet> x \<le> b $ i}" by auto
    ultimately have "F = {x. x \<in> carrier_vec n \<and> A' *\<^sub>v x = b' \<and> C *\<^sub>v x \<le> d \<and> row A i \<bullet> x \<le> b $ i}"
      using \<open>F = {x \<in> carrier_vec n. A' *\<^sub>v x = b' \<and> A'' *\<^sub>v x \<le> b''}\<close> by presburger
    have "{x. x \<in> carrier_vec n \<and> A' *\<^sub>v x = b' \<and> C *\<^sub>v x \<le> d \<and> row A i \<bullet> x \<le> b $ i} =
          {x. x \<in> carrier_vec n \<and> A' *\<^sub>v x = b' \<and> C *\<^sub>v x \<le> d}"
    proof(safe) 
      fix x
      assume "x \<in> carrier_vec n" "C *\<^sub>v x \<le> d" "b' = A' *\<^sub>v x" 
      obtain j where "j < dim_vec (snd (sub_system A b I)) \<and>
       row (fst (sub_system A b I)) j = row A i \<and> 
          (snd (sub_system A b I)) $ j = b $ i" using exist_index_in_A'[of A b i I] i
        using A \<open>dim_vec b = nr\<close> b by blast
      then have "row A' j = row A i \<and> b' $ j = b $ i" 
        by (metis fst_conv snd_conv sub_A(1))
      have "j < dim_row A'" 
        by (metis A \<open>j < dim_vec (snd (sub_system A b I)) \<and> row (fst (sub_system A b I)) j = row A i \<and> snd (sub_system A b I) $ j = b $ i\<close> b carrier_matD(1) carrier_vecD dims_subsyst_same prod.sel(1) sub_A(1))

      then have "b' $ j = row A' j \<bullet> x" using `b' = A' *\<^sub>v x` unfolding mult_mat_vec_def by simp
      then have "b $ i = row A i \<bullet> x" using `row A' j = row A i \<and> b' $ j = b $ i` by auto
      then show "row A i \<bullet> x \<le> b $ i" by auto
    qed
    then have "F = {x. x \<in> carrier_vec n \<and> A' *\<^sub>v x = b' \<and> C *\<^sub>v x \<le> d}" 
      using \<open>F = {x \<in> carrier_vec n. A' *\<^sub>v x = b' \<and> C *\<^sub>v x \<le> d \<and> row A i \<bullet> x \<le> b $ i}\<close> by fastforce
  
     then have "dim_vec d \<in> {dim_vec d| C d I.  (C, d) = sub_system A b I
                                  \<and> F = {x. x \<in> carrier_vec n \<and> A' *\<^sub>v x = b' \<and> C *\<^sub>v x \<le> d}}" 
       using `(C, d) = sub_system A b (I'' - {i})` by blast
   then have "dim_vec d \<ge> Min {dim_vec d| C d I.  (C, d) = sub_system A b I
                                  \<and> F = {x. x \<in> carrier_vec n \<and> A' *\<^sub>v x = b' \<and> C *\<^sub>v x \<le> d}}"
     using 2 by auto
   then have "dim_vec d \<ge> dim_vec b''" using `dim_vec b'' = Min {dim_vec d| C d I.  (C, d) = sub_system A b I 
                                  \<and> F = {x. x \<in> carrier_vec n \<and> A' *\<^sub>v x = b' \<and> C *\<^sub>v x \<le> d}}`
     by auto
   have "dim_vec d + 1 = dim_vec b''"
     using \<open>(A'', b'') = sub_system A b I''\<close> \<open>(C, d) = sub_system A b (I'' - {i})\<close> i remove_index_sub_system_dims 
     by (metis \<open>dim_vec b = nr\<close>)
   then have "dim_vec d < dim_vec b''" by auto
   then show False 
     using \<open>dim_vec b'' \<le> dim_vec d\<close> linorder_not_le by blast
 qed
  have "dim_vec b'' = 0" 
  proof(rule ccontr)
    assume "dim_vec b'' \<noteq> 0" 
    then have "dim_vec b'' > 0" by auto
  then obtain j where "j < dim_vec b''" by auto
  then obtain i where "i < nr \<and> i \<in> I'' \<and> row A'' j = row A i \<and> b'' $ j = b $ i" 
      using exist_index_in_A[of A  b j I''] 
      by (metis A \<open>(A'', b'') = sub_system A b I''\<close> \<open>dim_vec b = nr\<close> carrier_matD(1) fst_conv snd_conv)
    obtain C d where sub_C: "((C, d) = sub_system A b (I'' - {i}))" 
      by (metis surj_pair)
    have "{x. A'' *\<^sub>v x \<le> b''} = {x. C *\<^sub>v x \<le> d \<and> row A i \<bullet> x \<le> b $ i}"    
      using remove_index_sub_system[of A b i I'' A'' b''  C d]  
      using \<open>(A'', b'') = sub_system A b I''\<close> 
            \<open>(C, d) = sub_system A b (I'' - {i})\<close> \<open>i < nr \<and> i \<in> I'' \<and> row A'' j = row A i \<and> b'' $ j = b $ i\<close> 
      using A \<open>dim_vec b = nr\<close> by blast
    moreover have "{x. x \<in> carrier_vec n \<and> A' *\<^sub>v x = b' \<and> C *\<^sub>v x \<le> d \<and> row A i \<bullet> x \<le> b $ i} = 
      {x. x \<in> carrier_vec n \<and> A' *\<^sub>v x = b'} \<inter> {x.  C *\<^sub>v x \<le> d \<and> row A i \<bullet> x \<le> b $ i}"
      by blast
    moreover have "{x. x \<in> carrier_vec n \<and> A' *\<^sub>v x = b' \<and> A'' *\<^sub>v x \<le> b'' } = 
      {x. x \<in> carrier_vec n \<and> A' *\<^sub>v x = b'} \<inter> {x. A'' *\<^sub>v x \<le> b''}" by blast

    ultimately  have "{x. x \<in> carrier_vec n \<and> A' *\<^sub>v x = b' \<and> A'' *\<^sub>v x \<le> b'' } = 
      {x. x \<in> carrier_vec n \<and> A' *\<^sub>v x = b' \<and> C *\<^sub>v x \<le> d \<and> row A i \<bullet> x \<le> b $ i}" 
      by auto
    then have "F = {x. x \<in> carrier_vec n \<and> A' *\<^sub>v x = b' \<and> C *\<^sub>v x \<le> d \<and> row A i \<bullet> x \<le> b $ i}"
      using \<open>F = {x \<in> carrier_vec n. A' *\<^sub>v x = b' \<and> A'' *\<^sub>v x \<le> b''}\<close> by fastforce
    
    show False
    proof(cases "{x. x \<in> carrier_vec n \<and> A' *\<^sub>v x = b' \<and> C *\<^sub>v x \<le> d} \<inter> {x. row A i \<bullet> x > b $ i} = {}")
      case True
     
      have "{x. x \<in> carrier_vec n \<and> A' *\<^sub>v x = b' \<and> C *\<^sub>v x \<le> d \<and> row A i \<bullet> x \<le> b $ i} = 
          {x. x \<in> carrier_vec n \<and> A' *\<^sub>v x = b' \<and> C *\<^sub>v x \<le> d}" 
        using True by fastforce
      then have "F = {x. x \<in> carrier_vec n \<and> A' *\<^sub>v x = b' \<and> C *\<^sub>v x \<le> d}" 
        using \<open>F = {x \<in> carrier_vec n. A' *\<^sub>v x = b' \<and> C *\<^sub>v x \<le> d \<and> row A i \<bullet> x \<le> b $ i}\<close> by fastforce
     
      then have "(C, d) = sub_system A b (I'' - {i}) 
                                  \<and> F = {x. x \<in> carrier_vec n \<and> A' *\<^sub>v x = b' \<and> C *\<^sub>v x \<le> d}" 
     using `((C, d) = sub_system A b (I'' - {i}))` by auto
   then have "dim_vec d \<in> {dim_vec d| C d I.  (C, d) = sub_system A b I
                                  \<and> F = {x. x \<in> carrier_vec n \<and> A' *\<^sub>v x = b' \<and> C *\<^sub>v x \<le> d}}" 
     by auto 
   then have "dim_vec d \<ge> Min {dim_vec d| C d I.  (C, d) = sub_system A b I
                                  \<and> F = {x. x \<in> carrier_vec n \<and> A' *\<^sub>v x = b' \<and> C *\<^sub>v x \<le> d}}"
     using 2 by auto
   then have "dim_vec d \<ge> dim_vec b''" using `dim_vec b'' = Min {dim_vec d| C d I.  (C, d) = sub_system A b I 
                                  \<and> F = {x. x \<in> carrier_vec n \<and> A' *\<^sub>v x = b' \<and> C *\<^sub>v x \<le> d}}`
     by auto
   have "dim_vec d + 1 = dim_vec b''" using
    \<open>(A'', b'') = sub_system A b I''\<close> 
    \<open>(C, d) = sub_system A b (I'' - {i})\<close> 
    \<open>i < nr \<and> i \<in> I'' \<and> row A'' j = row A i \<and> b'' $ j = b $ i\<close> 
      remove_index_sub_system_dims 
     by (metis \<open>dim_vec b = nr\<close>)
   then have "dim_vec d < dim_vec b''" by auto
   
      
      then show ?thesis using `dim_vec d \<ge> dim_vec b''` by simp 
    next
      case False
      have "row A i \<in> carrier_vec n" 
        using A \<open>i < nr \<and> i \<in> I'' \<and> row A'' j = row A i \<and> b'' $ j = b $ i\<close> row_carrier_vec by blast
      then have "{x. x \<in> carrier_vec n \<and> A' *\<^sub>v x = b' \<and> C *\<^sub>v x \<le> d} \<inter> {x. row A i \<bullet> x > b $ i} \<noteq> {}" 
        using False  by simp
      then obtain y where "y \<in> {x. x \<in> carrier_vec n \<and> A' *\<^sub>v x = b' \<and> C *\<^sub>v x \<le> d} \<inter> {x. row A i \<bullet> x > b $ i}"
        by auto
      then have y:"y  \<in> carrier_vec n \<and> A' *\<^sub>v y = b' \<and> C *\<^sub>v y \<le> d \<and> row A i \<bullet> y > b $ i"  
        by fastforce
      then have "y \<in> carrier_vec n" by auto
      obtain x  where "x\<in> F" 
        by (metis \<open>face P F\<close> equals0I gram_schmidt.face_non_empty)
      then have x:"x \<in> carrier_vec n \<and> A' *\<^sub>v x = b' \<and> C *\<^sub>v x \<le> d \<and> row A i \<bullet> x \<le> b $ i" 
        using \<open>F = {x \<in> carrier_vec n. A' *\<^sub>v x = b' \<and> C *\<^sub>v x \<le> d \<and> row A i \<bullet> x \<le> b $ i}\<close> by fastforce
      then have "x \<in> carrier_vec n" by auto
      have "row A i \<bullet> x - row A i \<bullet> y \<noteq> 0" 
        using \<open>x \<in> carrier_vec n \<and> A' *\<^sub>v x = b' \<and> C *\<^sub>v x \<le> d \<and> row A i \<bullet> x \<le> b $ i\<close> \<open>y \<in> carrier_vec n \<and> A' *\<^sub>v y = b' \<and> C *\<^sub>v y \<le> d \<and> b $ i < row A i \<bullet> y\<close> by linarith

      let ?z = "y + ((b $ i - row A i \<bullet> y)/(row A i \<bullet> x - row A i \<bullet> y)) \<cdot>\<^sub>v (x - y)"
        have "row A i \<bullet> ?z = row A i \<bullet> y + row A i \<bullet> (((b $ i - row A i \<bullet> y)/(row A i \<bullet> x - row A i \<bullet> y)) \<cdot>\<^sub>v (x - y))" 
          
          by (meson \<open>row A i \<in> carrier_vec n\<close> \<open>x \<in> carrier_vec n\<close> \<open>y \<in> carrier_vec n\<close> minus_carrier_vec scalar_prod_add_distrib smult_closed)
        then have "row A i \<bullet> ?z = row A i \<bullet> y + ((b $ i - row A i \<bullet> y)/(row A i \<bullet> x - row A i \<bullet> y)) * (row A i \<bullet> (x - y))" 
            by (metis \<open>row A i \<in> carrier_vec n\<close> \<open>x \<in> carrier_vec n\<close> \<open>y \<in> carrier_vec n\<close> minus_carrier_vec scalar_prod_smult_distrib)
          then have "row A i \<bullet> ?z = row A i \<bullet> y + (b $ i - row A i \<bullet> y)" 
            by (metis \<open>row A i \<bullet> x - row A i \<bullet> y \<noteq> 0\<close> \<open>row A i \<in> carrier_vec n\<close> \<open>x \<in> carrier_vec n\<close> \<open>y \<in> carrier_vec n\<close> nonzero_eq_divide_eq scalar_prod_minus_distrib)
          then have "row A i \<bullet> ?z = b $ i" 
            by simp
          let ?l = "(b $ i - row A i \<bullet> y)/(row A i \<bullet> x - row A i \<bullet> y)"
        
          have "?z = y + ?l \<cdot>\<^sub>v (x - y)" by simp
          then have "?z =  y  + ?l  \<cdot>\<^sub>v x - ?l \<cdot>\<^sub>v y " 
            using smult_minus_distrib_vec[of x y ?l] \<open>x \<in> carrier_vec n\<close> \<open>y \<in> carrier_vec n\<close> by fastforce
          have "y  + ?l  \<cdot>\<^sub>v x - ?l \<cdot>\<^sub>v y = y   - ?l \<cdot>\<^sub>v y + ?l  \<cdot>\<^sub>v x" 
            using `y \<in> carrier_vec n` `x \<in> carrier_vec n` by auto
        
          have "1  \<cdot>\<^sub>v y = y" 
            by simp
          have "?z =  1  \<cdot>\<^sub>v y  - ?l \<cdot>\<^sub>v y  + ?l  \<cdot>\<^sub>v x" 
            apply (auto simp:`1  \<cdot>\<^sub>v y = y`)
            using `?z =  y  + ?l  \<cdot>\<^sub>v x - ?l \<cdot>\<^sub>v y ` 
            by (simp add: \<open>y + (b $ i - row A i \<bullet> y) / (row A i \<bullet> x - row A i \<bullet> y) \<cdot>\<^sub>v x - (b $ i - row A i \<bullet> y) / (row A i \<bullet> x - row A i \<bullet> y) \<cdot>\<^sub>v y = y - (b $ i - row A i \<bullet> y) / (row A i \<bullet> x - row A i \<bullet> y) \<cdot>\<^sub>v y + (b $ i - row A i \<bullet> y) / (row A i \<bullet> x - row A i \<bullet> y) \<cdot>\<^sub>v x\<close>)
          then have "?z = (1 - ?l) \<cdot>\<^sub>v y + ?l  \<cdot>\<^sub>v x"
            using diff_smult_distrib_vec[of 1 ?l y] `?z =  y  + ?l  \<cdot>\<^sub>v x - ?l \<cdot>\<^sub>v y `  
            by presburger
          have "0 < ?l" 
          proof - 
            have "b $ i - row A i \<bullet> y < 0" using y by auto
            have "row A i \<bullet> x - row A i \<bullet> y < 0" using y x by auto
            then show "0 < ?l" 
              using \<open>b $ i - row A i \<bullet> y < 0\<close> divide_neg_neg by blast
          qed
          have "?l \<le> 1" 
          proof -
            have "b $ i \<ge> row A i \<bullet> x" using x by auto
            then have " b $ i - row A i \<bullet> y \<ge> row A i \<bullet> x - row A i \<bullet> y"
              by auto
            then show "?l \<le> 1" 
              by (meson divide_le_eq_1_neg less_iff_diff_less_0 order_le_less_trans y)
          qed
            have "?z \<in> carrier_vec n" 
              by (simp add: \<open>x \<in> carrier_vec n\<close> \<open>y \<in> carrier_vec n\<close>)
            have " A' *\<^sub>v ?z = b'" 
            proof 
              {
                fix j
                assume "j < dim_vec b'"
                have "dim_col A' = n" using sub_A A dim_col_subsyst_mat 
                  by (metis carrier_matD(2) fst_conv)
                then have "row A' j \<in> carrier_vec n" 
                  using row_carrier by blast
                have "row A' j \<bullet> y = b' $ j" using y 
                  by (metis \<open>j < dim_vec b'\<close> dim_mult_mat_vec index_mult_mat_vec)
                then have "row A' j \<bullet> ((1 - ?l) \<cdot>\<^sub>v y) = (1 - ?l) * (b' $ j)"
                  using  `row A' j \<in> carrier_vec n`  `y \<in> carrier_vec n` by auto  

                 have "row A' j \<bullet> x = b' $ j" using x 
                  by (metis \<open>j < dim_vec b'\<close> dim_mult_mat_vec index_mult_mat_vec)
                then have "row A' j \<bullet> (?l \<cdot>\<^sub>v x) = ?l * (b' $ j)"
                  using  `row A' j \<in> carrier_vec n`  `x \<in> carrier_vec n` by auto  
                then have "row A' j \<bullet> ((1 - ?l) \<cdot>\<^sub>v y) + row A' j \<bullet> (?l \<cdot>\<^sub>v x) = 
                        (1 - ?l) * (b' $ j) + ?l * (b' $ j)" 
                  
                  using \<open>row A' j \<bullet> ((1 - (b $ i - row A i \<bullet> y) / (row A i \<bullet> x - row A i \<bullet> y)) \<cdot>\<^sub>v y) = (1 - (b $ i - row A i \<bullet> y) / (row A i \<bullet> x - row A i \<bullet> y)) * b' $ j\<close> by presburger
                then have "row A' j \<bullet> ((1 - ?l) \<cdot>\<^sub>v y + ?l \<cdot>\<^sub>v x) = 
                       (1 - ?l) * (b' $ j) + ?l * (b' $ j)" 
                  by (metis \<open>row A' j \<in> carrier_vec n\<close> \<open>x \<in> carrier_vec n\<close> \<open>y \<in> carrier_vec n\<close> scalar_prod_add_distrib smult_closed)
                then have "row A' j \<bullet> ?z = b' $ j" 
                  by (metis \<open>y + (b $ i - row A i \<bullet> y) / (row A i \<bullet> x - row A i \<bullet> y) \<cdot>\<^sub>v (x - y) = (1 - (b $ i - row A i \<bullet> y) / (row A i \<bullet> x - row A i \<bullet> y)) \<cdot>\<^sub>v y + (b $ i - row A i \<bullet> y) / (row A i \<bullet> x - row A i \<bullet> y) \<cdot>\<^sub>v x\<close> diff_add_cancel l_distr l_one)
                then show "(A' *\<^sub>v ?z) $ j = b' $ j" 
                  by (metis \<open>j < dim_vec b'\<close> dim_mult_mat_vec index_mult_mat_vec x) 
              } 
              show "dim_vec (A' *\<^sub>v ?z) = dim_vec b'" 
                by (metis dim_mult_mat_vec x)
            qed
            have " C *\<^sub>v ?z \<le> d" 
            proof -
              have "\<forall> j < dim_vec d. row C j \<bullet> ?z \<le> d $ j" 
              proof(rule+)
                fix j
                assume "j < dim_vec d"
                have "dim_col C = n" using sub_C A dim_col_subsyst_mat 
                  by (metis carrier_matD(2) fst_conv)
                then have "row C j \<in> carrier_vec n" 
                  using row_carrier by blast
                have "C *\<^sub>v y \<le> d" using y by blast
                then have "row C j \<bullet> y \<le> d $ j" 
                  unfolding mult_mat_vec_def 
                  by (metis \<open>C *\<^sub>v y \<le> d\<close> \<open>j < dim_vec d\<close> dim_vec index_mult_mat_vec less_eq_vec_def)
                then have "(1 - ?l) * (row C j \<bullet> y) \<le> (1 - ?l) * d $ j" 
                  using `?l \<le> 1`  
                  by (simp add: m_comm mult_right_mono)
                then have "row C j \<bullet> ((1 - ?l) \<cdot>\<^sub>v y) = (1 - ?l) * (row C j \<bullet> y)"
                  using  `row C j \<in> carrier_vec n`  `y \<in> carrier_vec n` by auto    
                then have "row C j \<bullet> ((1 - ?l) \<cdot>\<^sub>v y) \<le> (1 - ?l) * d $ j" 
                  using \<open>(1 - (b $ i - row A i \<bullet> y) / (row A i \<bullet> x - row A i \<bullet> y)) * (row C j \<bullet> y) \<le> (1 - (b $ i - row A i \<bullet> y) / (row A i \<bullet> x - row A i \<bullet> y)) * d $ j\<close> by presburger

                have "C *\<^sub>v x \<le> d" using x by blast
                then have "row C j \<bullet> x \<le> d $ j" 
                  unfolding mult_mat_vec_def 
                  by (metis \<open>C *\<^sub>v x \<le> d\<close> \<open>j < dim_vec d\<close> dim_vec index_mult_mat_vec less_eq_vec_def)
                then have "?l * (row C j \<bullet> x) \<le> ?l * d $ j" 
                  using `?l > 0` 
                  using mult_le_cancel_left_pos by blast
                then have "row C j \<bullet> (?l \<cdot>\<^sub>v x) = ?l * (row C j \<bullet> x)"
                  using  `row C j \<in> carrier_vec n`  `x \<in> carrier_vec n` by auto    
                then have "row C j \<bullet> (?l \<cdot>\<^sub>v x) \<le> ?l * d $ j" 
                  using `?l * (row C j \<bullet> x) \<le> ?l * d $ j` by presburger
                then have "row C j \<bullet> ((1 - ?l) \<cdot>\<^sub>v y) + row C j \<bullet> (?l \<cdot>\<^sub>v x) \<le> (1 - ?l) * d $ j + ?l * d $ j" 
                  using `row C j \<bullet> ((1 - ?l) \<cdot>\<^sub>v y) \<le> (1 - ?l) * d $ j` by auto
                then have "row C j \<bullet> ((1 - ?l) \<cdot>\<^sub>v y + ?l \<cdot>\<^sub>v x) \<le> (1 - ?l) * d $ j + ?l * d $ j" 
                  by (metis \<open>row C j \<in> carrier_vec n\<close> \<open>x \<in> carrier_vec n\<close> \<open>y \<in> carrier_vec n\<close> scalar_prod_add_distrib smult_closed)
                then show "row C j \<bullet> ?z \<le> d $ j"            
                  by (smt (verit, del_insts) R.add.m_comm \<open>y + (b $ i - row A i \<bullet> y) / (row A i \<bullet> x - row A i \<bullet> y) \<cdot>\<^sub>v (x - y) = (1 - (b $ i - row A i \<bullet> y) / (row A i \<bullet> x - row A i \<bullet> y)) \<cdot>\<^sub>v y + (b $ i - row A i \<bullet> y) / (row A i \<bullet> x - row A i \<bullet> y) \<cdot>\<^sub>v x\<close> add_diff_cancel_left' add_diff_eq comm_semiring_class.distrib m_comm r_one)
              qed
              have "dim_row C = dim_vec d" 
                by (metis A b carrier_matD(1) carrier_vecD dims_subsyst_same prod.sel(1) prod.sel(2) sub_C)
              then show ?thesis using `\<forall> j < dim_vec d. row C j \<bullet> ?z \<le> d $ j` unfolding mult_mat_vec_def 
                by (simp add: less_eq_vec_def)
            qed
            then have "?z \<in> {x \<in> carrier_vec n. A' *\<^sub>v x = b' \<and> C *\<^sub>v x \<le> d \<and> row A i \<bullet> x \<le> b $ i}" 
              by (simp add: \<open>A' *\<^sub>v (y + (b $ i - row A i \<bullet> y) / (row A i \<bullet> x - row A i \<bullet> y) \<cdot>\<^sub>v (x - y)) = b'\<close> \<open>row A i \<bullet> (y + (b $ i - row A i \<bullet> y) / (row A i \<bullet> x - row A i \<bullet> y) \<cdot>\<^sub>v (x - y)) = b $ i\<close> \<open>y + (b $ i - row A i \<bullet> y) / (row A i \<bullet> x - row A i \<bullet> y) \<cdot>\<^sub>v (x - y) \<in> carrier_vec n\<close>)
            then have "?z \<in> F" 
              using \<open>F = {x \<in> carrier_vec n. A' *\<^sub>v x = b' \<and> C *\<^sub>v x \<le> d \<and> row A i \<bullet> x \<le> b $ i}\<close> by presburger
            then have "?z \<in> P" using `face P F`  
              by (metis IntE gram_schmidt.face_def)
            have "i \<notin> I" using `I \<inter> I'' \<inter> {0..<nr}= {}` 
              using \<open>i < nr \<and> i \<in> I'' \<and> row A'' j = row A i \<and> b'' $ j = b $ i\<close>
              by fastforce
           obtain C' d'  where "(C', d') = sub_system A b (I \<union> {i})" 
             by (metis surj_pair)
           then have "{x. C' *\<^sub>v x = d'} = {x. A' *\<^sub>v x = b' \<and> row A i \<bullet> x = b $ i}" 
             using insert_sub_system_eq[of A b i  A' b' I  C' d'] \<open>i \<notin> I\<close> sub_A(1)
             using A \<open>dim_vec b = nr\<close> \<open>i < nr \<and> i \<in> I'' \<and> row A'' j = row A i \<and> b'' $ j = b $ i\<close> by blast
           then have "{x. C' *\<^sub>v x = d' \<and> x \<in> P} = {x. A' *\<^sub>v x = b' \<and> row A i \<bullet> x = b $ i \<and> x \<in> P}" 
             by blast
           have "?z \<in>  {x. A' *\<^sub>v x = b' \<and> row A i \<bullet> x = b $ i \<and> x \<in> P}" 
             using `?z \<in> P` 
             using \<open>A' *\<^sub>v (y + (b $ i - row A i \<bullet> y) / (row A i \<bullet> x - row A i \<bullet> y) \<cdot>\<^sub>v (x - y)) = b'\<close> \<open>row A i \<bullet> (y + (b $ i - row A i \<bullet> y) / (row A i \<bullet> x - row A i \<bullet> y) \<cdot>\<^sub>v (x - y)) = b $ i\<close> by blast
           then have "{x. C' *\<^sub>v x = d' \<and> x \<in> P} \<noteq> {}" 
             using \<open>{x. C' *\<^sub>v x = d' \<and> x \<in> P} = {x. A' *\<^sub>v x = b' \<and> row A i \<bullet> x = b $ i \<and> x \<in> P}\<close> by blast
           then have "face P {x. C' *\<^sub>v x = d' \<and> x \<in> P}" using char_face2 
             using P_def \<open>(C', d') = sub_system A b (I \<union> {i})\<close> assms(1) b by blast
           have "{x. C' *\<^sub>v x = d' \<and> x \<in> P} \<subseteq> F" 
             using \<open>{x. C' *\<^sub>v x = d' \<and> x \<in> P} = {x. A' *\<^sub>v x = b' \<and> row A i \<bullet> x = b $ i \<and> x \<in> P}\<close> sub_A(2) by blast
           then have "{x. C' *\<^sub>v x = d' \<and> x \<in> P} = F" 
             using \<open>face P {x. C' *\<^sub>v x = d' \<and> x \<in> P}\<close> assms(4) min_face_def by auto
           then have "(C', d') = sub_system A b (I\<union>{i}) \<and> F = {x. C' *\<^sub>v x = d' \<and> x \<in> P}" 
             using \<open>(C', d') = sub_system A b (I \<union> {i})\<close> by fastforce
           then have "dim_vec d' \<in> {dim_vec d| C d I.  (C, d) = sub_system A b I \<and> F = {x. C *\<^sub>v x = d \<and> x \<in> P}}"
             by blast
           then have "dim_vec d' \<le> Max {dim_vec d| C d I.  (C, d) = sub_system A b I \<and> F = {x. C *\<^sub>v x = d \<and> x \<in> P}}" 
             using "1" by auto
           then have "dim_vec d' \<le> dim_vec b'" 
             using sub_A(3) by presburger
           have "dim_vec d' = dim_vec b' + 1" using add_index_sub_system_dims 
             using \<open>(C', d') = sub_system A b (I \<union> {i})\<close> \<open>i \<notin> I\<close> sub_A(1) 
             using \<open>dim_vec b = nr\<close> \<open>i < nr \<and> i \<in> I'' \<and> row A'' j = row A i \<and> b'' $ j = b $ i\<close> by blast
        then show ?thesis 
          using \<open>dim_vec d' \<le> dim_vec b'\<close> by linarith
      qed
    qed 
    then have "\<exists> x. x\<in> {x.  A'' *\<^sub>v x \<le> b''}" 
      using \<open>F = {x \<in> carrier_vec n. A' *\<^sub>v x = b' \<and> A'' *\<^sub>v x \<le> b''}\<close> \<open>face P F\<close> face_non_empty by auto 
    then have "{x.  A'' *\<^sub>v x \<le> b''} = UNIV" using `dim_vec b'' = 0`
      by (metis (no_types, lifting) UNIV_eq_I dim_mult_mat_vec less_eq_vec_def mem_Collect_eq vec_of_dim_1) 
    then have "{x. x \<in> carrier_vec n \<and> A' *\<^sub>v x = b' \<and> A'' *\<^sub>v x \<le> b''}
                 = {x. x \<in> carrier_vec n \<and> A' *\<^sub>v x = b'}" 
      by blast
    then have " F = {x. x \<in> carrier_vec n \<and> A' *\<^sub>v x = b'}" 
      using \<open>F = {x \<in> carrier_vec n. A' *\<^sub>v x = b' \<and> A'' *\<^sub>v x \<le> b''}\<close> by fastforce
    then show "(\<And>A' b' I. F = {x \<in> carrier_vec n. A' *\<^sub>v x = b'} \<Longrightarrow> (A', b') = sub_system A b I \<Longrightarrow> thesis) \<Longrightarrow> thesis"
      using sub_A(1) by auto 
qed

end
end