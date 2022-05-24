theory Totally_Unimodular
  imports
    Integer_Polyhedron
    Integer_hull_f_to_a
begin

context gram_schmidt_floor
begin

definition tot_unimodular where
  "tot_unimodular A = (\<forall> B. (\<exists> I J. submatrix A I J = B) \<longrightarrow> det B \<in> {-1, 0, 1})"

definition pos_polyhedron where 
  "pos_polyhedron A b = {x. x \<in> carrier_vec n \<and> A *\<^sub>v x \<le> b \<and> x \<ge> 0\<^sub>v n}"

definition int_polyh where
  "int_polyh P = (integer_hull P = P)" 

lemma tot_unimod_entries:
  assumes "tot_unimodular A"
  shows "elements_mat A \<subseteq> {-1, 0, 1}"
  sorry

lemma pos_polyh_is_polyh:
   fixes A :: "'a  mat"
   assumes A: "A \<in> carrier_mat nr n"
   assumes "b \<in> carrier_vec nr"
   shows "pos_polyhedron A b = polyhedron (A @\<^sub>r - 1\<^sub>m n) (b @\<^sub>v 0\<^sub>v n)"
proof -
  have "{x. x \<in> carrier_vec n \<and> A *\<^sub>v x \<le> b \<and> x \<ge> 0\<^sub>v n} = 
        {x. x \<in> carrier_vec n \<and> (A @\<^sub>r - 1\<^sub>m n) *\<^sub>v x \<le> (b @\<^sub>v 0\<^sub>v n)}"
  proof safe
    have carr_mone:"- 1\<^sub>m n \<in> carrier_mat n n"
      by simp
    {   fix x
    assume asm: " A *\<^sub>v x \<le> b" "0\<^sub>v n \<le> x " "x \<in> carrier_vec n"
    then have " \<forall> i < n. x $ i \<ge> 0\<^sub>v n $ i" 
      by (metis Matrix.less_eq_vec_def carrier_vecD)
    then have "\<forall> i < n. x $ i \<ge> 0"
      using asm(2) unfolding zero_vec_def using index_vec[of _ n "(\<lambda>i. 0)"] 
      by simp
    then have "\<forall> i < n. unit_vec n i \<bullet> x \<ge> 0 "
      by (metis M.zero_closed Matrix.less_eq_vec_def asm(2) carrier_dim_vec scalar_prod_left_unit)
    then have "\<forall> i < n. - unit_vec n i \<bullet> x \<le> 0" 
      by (metis M.add.one_closed Matrix.less_eq_vec_def asm(2) carrier_vecD index_unit_vec(3) 
          minus_equation_iff neg_0_le_iff_le scalar_prod_uminus_left)
    then have "\<forall> i < n. row (- 1\<^sub>m n) i \<bullet> x \<le> 0" 
      by simp
    then have "(- 1\<^sub>m n) *\<^sub>v x \<le> 0\<^sub>v n" 
      by (simp add: Matrix.less_eq_vec_def)
    then show "(A @\<^sub>r - 1\<^sub>m n) *\<^sub>v x  \<le> b @\<^sub>v 0\<^sub>v n" using asm(1)
      append_rows_le[OF A carr_mone]
      using asm(3) assms(2) by presburger
  }
  fix x
  assume asm:"(A @\<^sub>r - 1\<^sub>m n) *\<^sub>v x \<le> b @\<^sub>v 0\<^sub>v n" "x \<in> carrier_vec n"
  show "A *\<^sub>v x \<le> b" using asm append_rows_le[OF A carr_mone]
    using assms(2) by blast
  have "(- 1\<^sub>m n) *\<^sub>v x \<le> 0\<^sub>v n" 
    using A append_rows_le asm(1) asm(2) assms(2) carr_mone by blast
  then have "\<forall> i < n. row (- 1\<^sub>m n) i \<bullet> x \<le> 0" 
    unfolding less_eq_vec_def
    by simp
  then have "\<forall> i < n. unit_vec n i \<bullet> x \<ge> 0 " 
    using asm(2) by force
  then have "\<forall> i < n. x $ i \<ge> 0" 
    by (simp add: asm(2))
  then show "0\<^sub>v n \<le> x" 
    by (metis M.add.one_closed asm(2) index_zero_vec(1) lesseq_vecI)
qed
  then show ?thesis unfolding pos_polyhedron_def polyhedron_def by auto
qed

lemma rows_append_append_lists:
  assumes A: "A \<in> carrier_mat nr1 n" 
  assumes B: "B \<in> carrier_mat nr2 n" 
  shows "rows (A @\<^sub>r B) = (rows A) @ (rows B)"
proof -
  have "length (rows (A @\<^sub>r B)) = length (rows A) + length (rows B)"
    by (simp add: append_rows_def)
  then have 1: "length (rows (A @\<^sub>r B)) = length ((rows A) @ (rows B))"
    by (metis length_append)
  have "\<forall> i < length (rows (A @\<^sub>r B)). rows (A @\<^sub>r B) ! i = ((rows A) @ (rows B)) ! i"
  proof safe
    fix i
    assume asmi: "i < length (rows (A @\<^sub>r B))"
    show "rows (A @\<^sub>r B) ! i = ((rows A) @ (rows B)) ! i" 
    proof(cases "i < nr1")
      case True
      have "rows (A @\<^sub>r B) ! i = row A i" 
        using asmi append_rows_nth(1)[OF A B True] by auto
      moreover have "((rows A) @ (rows B)) ! i = (rows A) ! i"
        by (metis A True carrier_matD(1) length_rows nth_append)
      ultimately show ?thesis 
        using A True by force
    next
      case False
     have "rows (A @\<^sub>r B) ! i = row B (i-nr1)" 
        using asmi append_rows_nth(2)[OF A B] False 
        by (metis A \<open>length (Matrix.rows (A @\<^sub>r B)) = length (Matrix.rows A) + length (Matrix.rows B)\<close> 
            add_diff_inverse_nat assms(2) carrier_matD(1) le_add1 length_rows nth_rows)
      moreover have "((rows A) @ (rows B)) ! i = (rows B) ! (i-nr1)"
        by (metis False assms(1) carrier_matD(1) length_rows nth_append)
      then show ?thesis
        by (metis False \<open>length (Matrix.rows (A @\<^sub>r B)) = length (Matrix.rows A) + length (Matrix.rows B)\<close>
            add_diff_cancel_left' asmi assms(1) calculation carrier_matD(1) le_add_diff_inverse2 length_rows less_diff_conv not_le nth_rows)
    qed
  qed
  then show ?thesis 
    using 1 nth_equalityI by blast
qed

lemma rows_append_union_rows:
  assumes A: "A \<in> carrier_mat nr1 n" 
  assumes B: "B \<in> carrier_mat nr2 n" 
  shows "set (rows (A @\<^sub>r B)) = set (rows A) \<union> set (rows B)"
  using rows_append_append_lists[OF A B] 
  by simp

lemma tot_unimod_append_unit_vec:
 fixes A :: "'a  mat"
   assumes A: "A \<in> carrier_mat nr n" 
   assumes "tot_unimodular A"
   shows "tot_unimodular (A @\<^sub>r mat_of_rows n [unit_vec n i])" (is "tot_unimodular ?B")
  unfolding tot_unimodular_def
proof rule
  fix B
  show " (\<exists>I J. submatrix (A @\<^sub>r mat_of_rows n [unit_vec n i])I J = B) \<longrightarrow> det B \<in> {- 1, 0, 1}" 
  proof
  assume "\<exists>I J. submatrix (A @\<^sub>r mat_of_rows n [unit_vec n i]) I J = B"
  then show "det B \<in> {-1,0,1}" 
  proof(cases "dim_row B \<noteq> dim_col B")
    case True
    then show ?thesis unfolding Determinant.det_def 
      by (meson insertCI)
  next
    case False
    then  have "dim_row B = dim_col B" by auto
    then show ?thesis sorry
  qed
  oops
proof(cases "i< n")
  case True
  then show ?thesis sorry
next
  case False
  then have "\<forall> j < n. unit_vec n i $ j = 0" 
    unfolding unit_vec_def by simp
 have 1: "rows (mat_of_rows n [unit_vec n i]) = [unit_vec n i]" 
    using mat_of_rows_rows 
  by simp
  have "unit_vec n i = 0\<^sub>v n" 
    by (metis \<open>\<forall>j<n. unit_vec n i $v j = 0\<close> carrier_dim_vec eq_vecI index_unit_vec(3)
        index_zero_vec(1) zero_carrier_vec)
 have "0\<^sub>v n \<in> set (rows (mat_of_rows n [unit_vec n i]))"
    by (simp only: 1;simp add: \<open>unit_vec n i = 0\<^sub>v n\<close>)
  then have  "0\<^sub>v n \<in> set (rows ?B)" using rows_append_union_rows 
    by (smt (verit, del_insts) "1" \<open>unit_vec n i = 0\<^sub>v n\<close> append_insert assms(1) 
        gram_schmidt_floor.rows_append_append_lists list.set_intros(1) list.simps(15) 
        mat_of_rows_carrier(1))
  then show ?thesis sorry
qed

lemma tot_unimod_append_one:
  assumes "tot_unimodular A"
  shows "tot_unimodular (A @\<^sub>r - 1\<^sub>m n)" 
  sorry

lemma tot_unimod_then_int_polyhedron:
  fixes A :: "'a  mat"
  assumes A: "A \<in> carrier_mat nr n"
  assumes AI: "A \<in> \<int>\<^sub>m"
  assumes tot_unimod: "tot_unimodular A"
  shows "\<forall> b \<in> carrier_vec nr. b \<in> \<int>\<^sub>v \<longrightarrow> int_polyh (pos_polyhedron A b)"
proof rule+
  fix b :: "'a vec"
  assume "b \<in> carrier_vec nr"
  assume "b \<in> \<int>\<^sub>v"
  show "int_polyh (pos_polyhedron A b)"
    unfolding int_polyh_def
  proof -
    let ?fullA = "A @\<^sub>r - 1\<^sub>m n"
    let ?fullb = "b @\<^sub>v 0\<^sub>v n" 
    have 1:"?fullA \<in> carrier_mat (nr+n) n" sorry
    have 2:"?fullb \<in> carrier_vec (nr+n)" sorry
    have 3:"?fullA \<in> \<int>\<^sub>m" sorry
    have 4:"?fullb \<in> \<int>\<^sub>v" sorry
    have " integer_hull (polyhedron ?fullA ?fullb) = polyhedron ?fullA ?fullb"
    proof(cases "polyhedron ?fullA ?fullb = {}")
      case True
      have "integer_hull {} = {}" 
        by (simp add: integer_hull_def)
      then show ?thesis 
        using True by presburger
    next
      case False
      have 5: "\<forall>x \<in> (polyhedron ?fullA ?fullb). \<forall> i < n. x $ i \<ge>0" sorry
      then have 6: " (\<forall>x\<in>local.polyhedron (A @\<^sub>r - 1\<^sub>m n) (b @\<^sub>v 0\<^sub>v n). \<forall>i<n. x $v i \<le> 0) \<or>
    (\<forall>x\<in>local.polyhedron (A @\<^sub>r - 1\<^sub>m n) (b @\<^sub>v 0\<^sub>v n). \<forall>i<n. 0 \<le> x $v i)" 
        by blast

    have "(\<forall> F. min_face (polyhedron ?fullA ?fullb) F \<longrightarrow> (\<exists> x \<in> F. x \<in> \<int>\<^sub>v))"
    proof safe
      fix F
      assume asm: "min_face (polyhedron ?fullA ?fullb) F"
      obtain A' b' I'  where A'b':"((A', b') = sub_system ?fullA ?fullb I')" 
        " F = {x. x \<in> carrier_vec n \<and> A' *\<^sub>v x = b'}"
        "dim_vec b' = Min {dim_vec d| C d I. F = {x. x \<in> carrier_vec n \<and> C *\<^sub>v x = d} \<and> 
                                           (C, d) = sub_system ?fullA ?fullb I}"
        using min_face_min_subsyst[OF 1 2] 
        using \<open>min_face (local.polyhedron (A @\<^sub>r - 1\<^sub>m n) (b @\<^sub>v 0\<^sub>v n)) F\<close> 
        by (smt (z3) Collect_cong)
      have "\<exists> x \<in> F. abs(det A') \<cdot>\<^sub>v x \<in>  \<int>\<^sub>v" 
        using min_face_has_int[OF 1 2 3 4 False 6 asm] A'b'
        by blast
      have "det A' \<noteq> 0" using bounded_min_faces_det_non_zero[OF 1 2 False 6 asm] A'b' by blast
      have 7:" \<exists> I J. submatrix ?fullA I J = A'" using A'b'(1)
        by (metis prod.sel(1) sub_system_fst)
      have "tot_unimodular ?fullA" 
        by (simp add: assms(3) tot_unimod_append_one)
      then have "det A' \<in> {-1, 0, 1}" unfolding tot_unimodular_def using 7 
        by presburger 
      then have "det A' = -1 \<or> det A' = 1"
        using \<open>Determinant.det A' \<noteq> 0\<close> by blast
      then have "abs (det A') = 1"
        by (metis abs_1 abs_neg_one)
      then have "\<exists> x \<in> F. 1 \<cdot>\<^sub>v x \<in>  \<int>\<^sub>v"
        using \<open>\<exists>x\<in>F. \<bar>Determinant.det A'\<bar> \<cdot>\<^sub>v x \<in> \<int>\<^sub>v\<close> by presburger
      then show "\<exists> x \<in> F. x \<in>  \<int>\<^sub>v"
        by auto
    qed
    then  show " integer_hull (polyhedron ?fullA ?fullb) = polyhedron ?fullA ?fullb"
      using min_face_iff_int_polyh[OF 1 2 3 4]
      by blast
  qed
    then show "integer_hull (pos_polyhedron A b) = pos_polyhedron A b"
      using pos_polyh_is_polyh
      using \<open>b \<in> carrier_vec nr\<close> assms(1) by presburger
  qed
qed
  

lemma tot_unimod_iff_int_polyhedron:
  fixes A :: "'a  mat"
  assumes A: "A \<in> carrier_mat nr n"
  assumes  AI: "A \<in> \<int>\<^sub>m"
  shows "tot_unimodular A \<longleftrightarrow> 
        (\<forall> b \<in> carrier_vec nr. b \<in> \<int>\<^sub>v \<longrightarrow> int_polyh (pos_polyhedron A b))"

end