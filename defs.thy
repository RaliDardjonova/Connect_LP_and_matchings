theory defs                         
  imports     Jordan_Normal_Form.Matrix
    Jordan_Normal_Form.Gram_Schmidt
    LLL_Basis_Reduction.Gram_Schmidt_2
  Jordan_Normal_Form.DL_Missing_Sublist
Linear_Inequalities.Integer_Hull
"HOL-Analysis.Determinants"
 "HOL-Combinatorics.Permutations"
                                    
begin

lemma det_0_iff_vec_prod_zero1: assumes A: "(A :: 'a :: idom Matrix.mat) \<in> carrier_mat n n"
  shows "Determinant.det A = 0 \<longleftrightarrow> (\<exists> v. v \<in> carrier_vec n \<and> v \<noteq> 0\<^sub>v n \<and> A *\<^sub>v v = 0\<^sub>v n)"
  using det_0_iff_vec_prod_zero assms by auto

definition
  unit_vec1 :: "nat \<Rightarrow> nat \<Rightarrow> ('b :: zero_neq_one) Matrix.vec"
  where "unit_vec1 n i = Matrix.vec n (\<lambda> j. if j = i then 1 else 0)"

no_notation one_mat ( "1\<^sub>m")

definition one_mat1 :: "nat \<Rightarrow> 'a :: {zero,one} Matrix.mat" ("1\<^sub>m") where
  "1\<^sub>m n \<equiv> Matrix.mat n n (\<lambda> (i,j). if i = j then 1 else 0)"

proposition  cramer:
  fixes A ::"'a::{field}^'n^'n"
  assumes d0: "det A \<noteq> 0"
  shows "A *v x = b \<longleftrightarrow> x = (\<chi> k. det(\<chi> i j. if j=k then b$i else A$i$j) / det A)"
proof -
  from d0 obtain B where B: "A ** B = mat 1" "B ** A = mat 1"
    unfolding invertible_det_nz[symmetric] invertible_def
    by blast
  have "(A ** B) *v b = b"
    by (simp add: B)
  then have "A *v (B *v b) = b"
    by (simp add: matrix_vector_mul_assoc)
  then have xe: "\<exists>x. A *v x = b"
    by blast
  {
    fix x
    assume x: "A *v x = b"
    have "x = (\<chi> k. det(\<chi> i j. if j=k then b$i else A$i$j) / det A)"
      unfolding x[symmetric]
      using d0 by (simp add: vec_eq_iff cramer_lemma field_simps)
  }
  with xe show ?thesis
    by auto
qed

no_notation inner (infix "\<bullet>" 70)
no_notation Finite_Cartesian_Product.vec.vec_nth (infixl "$" 90)

context gram_schmidt_floor
begin 

definition "mat_delete1 A i j \<equiv>
  Matrix.mat (dim_row A - 1) (dim_col A - 1) (\<lambda>(i',j').
    A $$ (if i' < i then i' else Suc i', if j' < j then j' else Suc j'))"



corollary integer_hull_of_polyhedron1: assumes A: "A \<in> carrier_mat nr n"
  and b: "b \<in> carrier_vec nr"
  and AI: "A \<in> \<int>\<^sub>m"
  and bI: "b \<in> \<int>\<^sub>v"
  and P: "P = polyhedron A b"
shows "\<exists> A' b' nr'. A' \<in> carrier_mat nr' n \<and> b' \<in> carrier_vec nr' \<and> integer_hull P = polyhedron A' b'"
proof -
  from decomposition_theorem_integer_hull_of_polyhedron[OF A b AI bI P refl]
  obtain H C
    where HC: "H \<union> C \<subseteq> carrier_vec n \<inter> \<int>\<^sub>v" "finite (H \<union> C)" 
      and decomp: "integer_hull P = convex_hull H + cone C" by auto
  show ?thesis
    by (rule decomposition_theorem_polyhedra_2[OF _ _ _ _ decomp], insert HC, auto)
qed
end


fun pick :: "nat set \<Rightarrow> nat \<Rightarrow> nat" where
"pick S 0 = (LEAST a. a\<in>S)" |
"pick S (Suc n) = (LEAST a. a\<in>S \<and> a > pick S n)"



lift_definition dim_row :: "'a mat \<Rightarrow> nat" is fst .
lift_definition dim_col :: "'a mat \<Rightarrow> nat" is "fst o snd" .
definition carrier_mat :: "nat \<Rightarrow> nat \<Rightarrow> 'a mat set"
  where "carrier_mat nr nc = { m . dim_row m = nr \<and> dim_col m = nc}"

definition undef_vec :: "nat \<Rightarrow> 'a" where
  "undef_vec i \<equiv> [] ! i"

definition mk_vec :: "nat \<Rightarrow> (nat \<Rightarrow> 'a) \<Rightarrow> (nat \<Rightarrow> 'a)" where
  "mk_vec n f \<equiv> \<lambda> i. if i < n then f i else undef_vec (i - n)"

typedef 'a vec = "{(n, mk_vec n f) | n f :: nat \<Rightarrow> 'a. True}"
  by auto

definition mk_mat :: "nat \<Rightarrow> nat \<Rightarrow> (nat \<times> nat \<Rightarrow> 'a) \<Rightarrow> (nat \<times> nat \<Rightarrow> 'a)" where
  "mk_mat nr nc f \<equiv> \<lambda> (i,j). if i < nr \<and> j < nc then f (i,j) else undef_mat nr nc f (i,j)"

lemma cong_mk_mat: assumes "\<And> i j. i < nr \<Longrightarrow> j < nc \<Longrightarrow> f (i,j) = f' (i,j)"
  shows "mk_mat nr nc f = mk_mat nr nc f'"
  using undef_cong_mat[of nr nc f f', OF assms]
  using assms unfolding mk_mat_def
  by auto

typedef 'a mat = "{(nr, nc, mk_mat nr nc f) | nr nc f :: nat \<times> nat \<Rightarrow> 'a. True}"
  by auto

locale gram_schmidt1 = cof_vec_space n f_ty
  for n :: nat and f_ty :: "'a :: {trivial_conjugatable_linordered_field} itself"
begin

definition "nonneg_lincomb c Vs b = (lincomb c Vs = b \<and> c ` Vs \<subseteq> {x. x \<ge> 0})"
definition "nonneg_lincomb_list c Vs b = (lincomb_list c Vs = b \<and> (\<forall> i < length Vs. c i \<ge> 0))"
definition "convex_lincomb c Vs b = (nonneg_lincomb c Vs b \<and> sum c Vs = 1)"
definition "convex_lincomb_list c Vs b = (nonneg_lincomb_list c Vs b \<and> sum c {0..<length Vs} = 1)"
definition "convex_hull Vs = {x. \<exists> Ws c. finite Ws \<and> Ws \<subseteq> Vs \<and> convex_lincomb c Ws x}"
definition "convex S = (convex_hull S = S)"
definition "polyhedron A b = {x \<in> carrier_vec n. A *\<^sub>v x \<le> b}"

definition "integer_hull P = convex_hull (P \<inter> \<int>\<^sub>v)"
end


end