theory Integer_Polyhedron
  imports Faces
    Well_Quasi_Orders.Minimal_Elements
    Linear_Inequalities.Integer_Hull
     Linear_Inequalities.Farkas_Lemma
    Missing_Sums 
    "HOL.Rat"
begin

context gram_schmidt
begin

lemma all_elem_fulfill_empty:
  assumes "(A', b') = sub_system A b {}"
  shows "A' *\<^sub>v x = b'" 
proof
  have "A' = submatrix A {} UNIV" 
    by (metis assms fst_conv sub_system_fst)
  then have "dim_row A' = 0" 
    by (simp add: dim_submatrix(1))
  have "b' = vec_of_list (nths (list_of_vec b) {})" 
    by (metis assms snd_conv sub_system_snd)
  then have "dim_vec b' = 0" 
    by fastforce
  show "dim_vec (A' *\<^sub>v x) = dim_vec b'" 
    by (simp add: \<open>dim_row A' = 0\<close> \<open>dim_vec b' = 0\<close>)
  show "\<And>i. i < dim_vec b' \<Longrightarrow>
         (A' *\<^sub>v x) $ i = b' $ i" 
    using \<open>dim_vec b' = 0\<close> by linarith
qed


lemma subsyst_with_max_ineq:
  fixes A :: "'a :: trivial_conjugatable_linordered_field mat"
  assumes A: "A \<in> carrier_mat nr n"
  assumes b: "b \<in> carrier_vec nr"
  defines "P \<equiv> polyhedron A b"
  assumes "P \<noteq> {}"
  obtains A' b' I'  where "((A', b') = sub_system A b I')" 
    "{x. A' *\<^sub>v x = b' \<and> x \<in> P} \<noteq> {}"
    "dim_vec b' = Max {dim_vec d| C d I. (C, d) = sub_system A b I \<and> 
                                                {x. C *\<^sub>v x = d \<and> x \<in> P} \<noteq> {}}"

proof-
  have "dim_vec b = nr" using b by auto
  let ?M = "{dim_vec d| C d I. (C, d) = sub_system A b I \<and> {x. C *\<^sub>v x = d \<and> x \<in> P} \<noteq> {}}"
  have "finite ?M"
    using subset_set_of_sub_dims_finite[of ?M A b] by blast
  let ?emp_A = "fst (sub_system A b {})"
  let ?emp_b = "snd (sub_system A b {})" 
  have "{x. ?emp_A *\<^sub>v x = ?emp_b \<and> x \<in> P} = P" 
    by (smt (verit, ccfv_SIG) Collect_cong P_def all_elem_fulfill_empty mem_Collect_eq polyhedron_def prod.collapse)
  then have "dim_vec ?emp_b \<in> ?M" using assms(4) 
    by (smt (verit, best) Collect_cong mem_Collect_eq prod.collapse)

  then have "?M \<noteq> {}"  
    by blast
  then have "Max ?M \<in> ?M \<and> (\<forall>a \<in> ?M. a \<le> (Max ?M))"
    using eq_Max_iff[of ?M] `?M \<noteq> {}` `finite ?M` 
    by auto
  then show ?thesis 
    using that by force
qed

lemma submatrix_same_I_interesect_rows:
  shows "submatrix A I UNIV = submatrix A (I \<inter> {0..<dim_row A}) UNIV"
proof
  show "dim_row (submatrix A I UNIV) = dim_row (submatrix A (I \<inter> {0..<dim_row A}) UNIV)" 
    using dim_submatrix 
    by (smt (verit) Collect_cong Int_iff atLeastLessThan_iff less_nat_zero_code linorder_le_less_linear)

  show "dim_col (submatrix A I UNIV) = dim_col (submatrix A (I \<inter> {0..<dim_row A}) UNIV)" 
    using dim_submatrix 
    by (smt (verit) Collect_cong Int_iff atLeastLessThan_iff less_nat_zero_code linorder_le_less_linear)

  show "\<And>i j. i < dim_row (submatrix A (I \<inter> {0..<dim_row A}) UNIV) \<Longrightarrow>
           j < dim_col (submatrix A (I \<inter> {0..<dim_row A}) UNIV) \<Longrightarrow>
           submatrix A I UNIV $$ (i, j) = submatrix A (I \<inter> {0..<dim_row A}) UNIV $$ (i, j)" 
  proof -
    fix i j
    assume "i < dim_row (submatrix A (I \<inter> {0..<dim_row A}) UNIV)" 
    assume "j < dim_col (submatrix A (I \<inter> {0..<dim_row A}) UNIV)" 
    have "submatrix A I UNIV $$ (i, j) = A $$ (pick I i, pick UNIV j)" using submatrix_index
      by (metis (no_types, lifting) \<open>dim_row (submatrix A I UNIV) = dim_row (submatrix A (I \<inter> {0..<dim_row A}) UNIV)\<close> \<open>i < dim_row (submatrix A (I \<inter> {0..<dim_row A}) UNIV)\<close> \<open>j < dim_col (submatrix A (I \<inter> {0..<dim_row A}) UNIV)\<close> dim_submatrix(1) dim_submatrix(2))
    have "{a. a < dim_row A \<and> a \<in> I} = (I \<inter> {0..<dim_row A})" 
      by fastforce
    have "i < card {a. a < dim_row A \<and> a \<in> I}"
      by (metis  \<open>dim_row (submatrix A I UNIV) = dim_row (submatrix A (I \<inter> {0..<dim_row A}) UNIV)\<close> \<open>i < dim_row (submatrix A (I \<inter> {0..<dim_row A}) UNIV)\<close> dim_submatrix(1))

    then have "pick (I  \<inter> {0..<dim_row A}) i= pick I i"
      using pick_reduce_set[of i "dim_row A" I] `{a. a < dim_row A \<and> a \<in> I} = (I \<inter> {0..<dim_row A})`
      by presburger
    then show " submatrix A I UNIV $$ (i, j) = submatrix A (I \<inter> {0..<dim_row A}) UNIV $$ (i, j)"
      by (metis (no_types, lifting) \<open>i < dim_row (submatrix A (I \<inter> {0..<dim_row A}) UNIV)\<close> \<open>j < dim_col (submatrix A (I \<inter> {0..<dim_row A}) UNIV)\<close> \<open>submatrix A I UNIV $$ (i, j) = A $$ (pick I i, pick UNIV j)\<close> dim_submatrix(1) dim_submatrix(2) submatrix_index)
  qed
qed

lemma nths_intersect_length_same:
  shows "(nths l I) = (nths l {a. a < (length l) \<and> a \<in> I})" 
proof -
  have "\<forall> p \<in> set (zip l [0..<length l]). snd p \<in> I \<longleftrightarrow> snd p \<in> {a. a < length l \<and> a \<in> I}" 
    using zip_snd by force
  then have "filter (\<lambda>p. snd p \<in> I) (zip l [0..<length l]) = 
            filter (\<lambda>p. snd p \<in> {a. a < length l \<and> a \<in> I}) (zip l [0..<length l])"
    by (metis (mono_tags, lifting) filter_cong)
  then show ?thesis 
    unfolding nths_def by argo
qed



lemma same_subsyst_I_intersect_rows:
  assumes A: "A \<in> carrier_mat nr n"
  assumes b: "b \<in> carrier_vec nr"
  shows "sub_system A b I = sub_system A b (I \<inter> {0..<nr})"
proof
  have "submatrix A I UNIV = submatrix A (I \<inter> {0..<dim_row A}) UNIV" 
    using submatrix_same_I_interesect_rows by blast

  then show  "fst (sub_system A b I) = fst (sub_system A b (I \<inter> {0..<nr}))" 
    using A 
    by (metis carrier_matD(1) sub_system_fst)
  have "(nths (list_of_vec b) I) = (nths (list_of_vec b) {a. a < dim_vec b \<and> a \<in> I})"
    using nths_intersect_length_same 
    by (metis  Matrix.length_list_of_vec)
  then have "vec_of_list (nths (list_of_vec b) I) = 
      vec_of_list (nths (list_of_vec b) (I\<inter> {0..<dim_vec b}))" 
    by (smt (verit, best) Collect_cong Int_iff Matrix.length_list_of_vec atLeastLessThan_iff nths_intersect_length_same zero_order(1))
  then show "snd (sub_system A b I) = snd (sub_system A b (I \<inter> {0..<nr}))"
    by (metis b carrier_vecD sub_system_snd)
qed


lemma obtain_I_for_subface:
  fixes A :: "'a :: trivial_conjugatable_linordered_field mat"
  assumes A: "A \<in> carrier_mat nr n"
  assumes b: "b \<in> carrier_vec nr"
  defines "P \<equiv> polyhedron A b"
  assumes "((A', b') = sub_system A b I)" 
  assumes "F = {x. A' *\<^sub>v x = b' \<and> x \<in> P}"
  assumes "face P F"
  assumes "face P F'"
  assumes "F' \<subset> F"
  obtains C d I' where "((C, d) = sub_system A b I')" 
    "F' = {x. C *\<^sub>v x = d \<and> x \<in> P}" "(I \<inter> {0..<nr}) \<subset> (I' \<inter> {0..<nr})"
proof -
  obtain C d J where C_d:"((C, d) = sub_system A b J)" 
    "F' = {x. C *\<^sub>v x = d \<and> x \<in> P}" using char_face1 
    using A P_def assms(7) b by blast
  obtain C' d' where  C'_d':"((C', d') = sub_system A b (J \<union> I))" 
    by (metis surj_pair)
  have "dim_row A = dim_vec b" using A b 
    by (metis carrier_matD(1) carrier_vecD)
  have "{x. C *\<^sub>v x = d \<and> x \<in> P} = {x. C' *\<^sub>v x = d' \<and> x \<in> P}"
  proof(safe)
    {
      fix x
      assume "x \<in> P" "d = C *\<^sub>v x"  
      have "x \<in> F" 
        using C_d(2) \<open>d = C *\<^sub>v x\<close> \<open>x \<in> P\<close> assms(8) by blast
      then have "A' *\<^sub>v x = b'" using assms(5) by auto
      then have "\<forall>i < dim_row A'. row A' i \<bullet> x = b' $ i" 
        by (metis index_mult_mat_vec)
      then have "\<forall>i \<in> I \<inter> {0..<dim_row A}.  (row A i) \<bullet> x = (b $ i)"
        using subsystem_fulfills_P[of A b A' b' I "\<lambda> p q. p \<bullet> x = q"] assms(4)
          `dim_row A = dim_vec b`  by blast

      have "\<forall>i < dim_row C. row C i \<bullet> x = d $ i" using `d = C *\<^sub>v x`
        by (metis index_mult_mat_vec)
      then have "\<forall>i \<in> J \<inter> {0..<dim_row A}.  (row A i) \<bullet> x = (b $ i)"
        using subsystem_fulfills_P[of A b C d J "\<lambda> p q. p \<bullet> x = q"] C_d
          `dim_row A = dim_vec b`  by blast
      then have "\<forall>i \<in> (I \<union> J) \<inter> {0..<dim_row A}. (row A i) \<bullet> x = (b $ i)"
        by (metis Int_Un_distrib2 Un_iff \<open>\<forall>i\<in>I \<inter> {0..<dim_row A}. row A i \<bullet> x = b $ i\<close>)
      then have "\<forall>i < dim_row C'. row C' i \<bullet> x = d' $ i" 
        using subsystem_fulfills_P'[of A b C' d' _ "\<lambda> p q. p \<bullet> x = q"] C'_d'
        using \<open>dim_row A = dim_vec b\<close> by blast
      then show "C' *\<^sub>v x = d'" 
        by (meson C'_d' \<open>dim_row A = dim_vec b\<close> dims_subsyst_same' eq_for_all_index_then_eq)
    }
    fix x
    assume "x \<in> P" "d' = C' *\<^sub>v x"
    then have "\<forall>i < dim_row C'. row C' i \<bullet> x = d' $ i"
      by (metis index_mult_mat_vec)
    then have "\<forall>i \<in> (I \<union> J) \<inter> {0..<dim_row A}. (row A i) \<bullet> x = (b $ i)"
      using subsystem_fulfills_P[of A b C' d' _ "\<lambda> p q. p \<bullet> x = q"] C'_d'
      using \<open>dim_row A = dim_vec b\<close> by blast
    then have "\<forall>i \<in> J \<inter> {0..<dim_row A}.  (row A i) \<bullet> x = (b $ i)" by auto
    then have "\<forall>i < dim_row C. row C i \<bullet> x = d $ i"
      using subsystem_fulfills_P'[of A b C d J "\<lambda> p q. p \<bullet> x = q"] C_d
        `dim_row A = dim_vec b`  by blast
    then show "C *\<^sub>v x = d"
      by (meson C_d \<open>dim_row A = dim_vec b\<close> dims_subsyst_same' eq_for_all_index_then_eq)
  qed  
  then have "F' = {x. C' *\<^sub>v x = d' \<and> x \<in> P}" using C_d by auto
  have "(I \<inter> {0..<nr}) \<subseteq> ((J \<union> I) \<inter> {0..<nr})" 
    by blast
  have "(I \<inter> {0..<nr}) \<noteq> ((J \<union> I) \<inter> {0..<nr})"
  proof
    assume "I \<inter> {0..<nr} = (J \<union> I) \<inter> {0..<nr}" 
    then have "sub_system A b I = sub_system A b (J \<union> I)" 
      by (metis A b gram_schmidt.same_subsyst_I_intersect_rows)
    then have "{x. A' *\<^sub>v x = b' \<and> x \<in> P} = {x. C *\<^sub>v x = d \<and> x \<in> P}" 
      by (metis (no_types, lifting)  Pair_inject \<open>(C', d') = sub_system A b (J \<union> I)\<close> \<open>{x. C *\<^sub>v x = d \<and> x \<in> P} = {x. C' *\<^sub>v x = d' \<and> x \<in> P}\<close> assms(4))
    then show False using assms(8) 
      using C_d(2) assms(5) by blast
  qed
  then have "(I \<inter> {0..<nr}) \<subset> ((J \<union> I) \<inter> {0..<nr})" 
    by blast
  then show ?thesis using C'_d' `F' = {x. C' *\<^sub>v x = d' \<and> x \<in> P}` 
    using that by presburger
qed

lemma less_I_less_dims_subsystem:
  assumes A: "A \<in> carrier_mat nr n"
  assumes b: "b \<in> carrier_vec nr"
  assumes "(I \<inter> {0..<nr}) \<subset> (J \<inter> {0..<nr})" 
  assumes "((A', b') = sub_system A b I)"
  assumes  "((C, d) = sub_system A b J)"
  shows "dim_row A' < dim_row C"
    "dim_vec b' < dim_vec d" 
proof -
  have "sub_system A b I = sub_system A b (I \<inter> {0..<nr})"
    using same_subsyst_I_intersect_rows A b 
    by blast
  then have "dim_row A' = card (I \<inter> {0..<nr})" using I_subsys_same_card(2)
    by (metis (mono_tags, lifting) A assms(4) b carrier_matD(1) carrier_vecD dims_subsyst_same' inf.cobounded2 snd_conv)

  have "sub_system A b J = sub_system A b (J \<inter> {0..<nr})"
    using same_subsyst_I_intersect_rows A b 
    by blast
  then have "dim_row C = card (J \<inter> {0..<nr})" using I_subsys_same_card(2)
    by (metis (mono_tags, lifting) A assms(5) b carrier_matD(1) carrier_vecD dims_subsyst_same' inf.cobounded2 snd_conv)
  have "finite (J \<inter> {0..<nr})" 
    by blast
  then have "card (I \<inter> {0..<nr}) < card (J \<inter> {0..<nr})" 
    by (meson assms(3) psubset_card_mono)
  then show "dim_row A' < dim_row C" 
    using \<open>dim_row A' = card (I \<inter> {0..<nr})\<close> \<open>dim_row C = card (J \<inter> {0..<nr})\<close> by presburger
  have "dim_row A' = dim_vec b'" 
    by (metis A assms(4) b carrier_matD(1) carrier_vecD dims_subsyst_same')
  have "dim_row C = dim_vec d" 
    by (metis A assms(5) b carrier_matD(1) carrier_vecD dims_subsyst_same')
  then show "dim_vec b' < dim_vec d" 
    using \<open>dim_row A' < dim_row C\<close> \<open>dim_row A' = dim_vec b'\<close> by presburger
qed

lemma append_rows_index_same:
  fixes A :: "'a :: trivial_conjugatable_linordered_field mat"
  assumes A: "A \<in> carrier_mat nr1 n"
  assumes "B \<in> carrier_mat nr2 n" 
  shows "\<forall> i < dim_row A. (row (A @\<^sub>r B)i) = row A i" 
  by (metis A append_rows_nth(1) assms(2) carrier_matD(1))

lemma append_rows_index_same':
  fixes A :: "'a :: trivial_conjugatable_linordered_field mat"
  assumes A: "A \<in> carrier_mat nr1 n"
  assumes "B \<in> carrier_mat nr2 n" 
  shows "\<lbrakk> i \<ge> nr1; i < nr1 + nr2 \<rbrakk> \<Longrightarrow> (row (A @\<^sub>r B)i) = row B (i - nr1)" 
  by (metis A append_rows_nth(2) assms(2))



lemma face_trans:
  fixes A :: "'a :: trivial_conjugatable_linordered_field mat"
  assumes A: "A \<in> carrier_mat nr n"
  assumes b: "b \<in> carrier_vec nr"
  defines "P \<equiv> polyhedron A b"
  assumes "face P F"
  assumes "face F F'"
  shows "face P F'"
proof -
  obtain A' b' I' where A'_b':"((A', b') = sub_system A b I')
                              \<and> F = {x. A' *\<^sub>v x = b' \<and> x \<in> P}"
    using char_face1[of A nr b F] assms(1-4) 
    unfolding P_def 
    by (metis (full_types))
  then obtain C d  where C_d:"C = (A @\<^sub>r(A' @\<^sub>r (-A')))" "d = (b @\<^sub>v (b' @\<^sub>v (-b')))"  
    "F = polyhedron C d"
    "dim_row (A @\<^sub>r (A' @\<^sub>r (-A'))) = dim_vec (b @\<^sub>v(b' @\<^sub>v (-b')))"
    "dim_col (A @\<^sub>r(A' @\<^sub>r (-A'))) = n"
    using face_is_polyhedron''2[of A nr b A' b' I' F] 
    by (smt (verit) A Collect_cong P_def b gram_schmidt.polyhedron_def mem_Collect_eq)

  then obtain C' d' J where C'_d': "((C', d') = sub_system C d J)
                              \<and> F' = {x. C' *\<^sub>v x = d' \<and> x \<in> F}"
    using char_face1[of C _ d F'] assms(1-5) 
    unfolding `F = polyhedron C d` 
    by (smt (verit, best) carrier_matI carrier_vec_dim_vec)

  obtain A'' b'' where A''_b'': "((A'', b'') = sub_system A b (I' \<union> J))" 
    by (metis surj_pair)
  have "dim_row A'' = dim_vec b''" 
    by (metis A A''_b'' b carrier_matD(1) carrier_vecD dims_subsyst_same')
  have "dim_row A \<le> dim_row C" using C_d 
    by (metis A add_lessD1 b carrier_matD(1) carrier_vecD index_append_vec(2) linorder_le_less_linear order_less_irrefl)
  have "\<forall> i < dim_row A. (row C i) = row A i" 
    using C_d(1) append_rows_index_same[of A nr "A' @\<^sub>r - A'" _]  

    by (metis (no_types, lifting) A \<open>(A', b') = sub_system A b I' \<and> F = {x. A' *\<^sub>v x = b' \<and> x \<in> P}\<close> b carrier_matI face_is_polyhedron'(3))
  have "\<forall> i < dim_vec b. d $ i = b $ i" 
    unfolding C_d(2)
    by (meson index_append_vec(1) trans_less_add1)
  then have "\<forall> i < dim_row A. (row C i) = row A i \<and> d $ i = b $ i" 
    by (metis A \<open>\<forall>i<dim_row A. row C i = row A i\<close> b carrier_matD(1) carrier_vecD)
  have "dim_row A' = dim_vec b'" 
    by (metis A A'_b' b carrier_matD(1) carrier_vecD dims_subsyst_same')
  have "dim_col A' = n" using A'_b' dim_col_subsyst_mat 
    by (metis A carrier_matD(2) fst_conv) 
  then have "dim_col (A' @\<^sub>r - A') = n" 
    using A A'_b' b face_is_polyhedron'(3) by blast
  then have "A' @\<^sub>r - A' \<in> carrier_mat (dim_row (A' @\<^sub>r - A')) n" 
    by blast
  have "dim_row C = nr + dim_row (A' @\<^sub>r - A')" 
    using A A'_b' C_d(1) C_d(4) b face_is_polyhedron'(2) by force
  have "\<forall> i. (i \<ge> nr \<and> i < dim_row C) \<longrightarrow> (row C i) = row  (A' @\<^sub>r - A') (i - nr)" 
    using C_d(1) append_rows_index_same'[of A nr "A' @\<^sub>r - A'" "dim_row (A' @\<^sub>r - A')"] 
      `A' @\<^sub>r - A' \<in> carrier_mat (dim_row (A' @\<^sub>r - A')) n` A
    by (metis \<open>dim_row C = nr + dim_row (A' @\<^sub>r - A')\<close>)
  have "\<forall> i. i > nr \<and> i < dim_vec d \<longrightarrow> d $ i =  (b' @\<^sub>v (-b')) $ (i - nr)" 
    unfolding C_d(2) 
    using b by auto
  then have "\<forall> i \<in> {nr..<dim_row C}. (row C i) = row  (A' @\<^sub>r - A') (i - nr) 
\<and> d $ i =  (b' @\<^sub>v (-b')) $ (i - nr)" 
    by (metis C_d(1) C_d(2) C_d(4) \<open>\<forall>i. nr \<le> i \<and> i < dim_row C \<longrightarrow> row C i = row (A' @\<^sub>r - A') (i - nr)\<close> atLeastLessThan_iff b carrier_vecD index_append_vec(1) index_append_vec(2) order_le_imp_less_or_eq)

  have " \<forall> x \<in> F. A' *\<^sub>v x = b' "using A'_b' by auto
  then have "\<forall> x \<in> F. \<forall>i < dim_row A'. row A' i \<bullet> x = b' $ i" 
    using index_mult_mat_vec
    by metis
  then have "\<forall> x \<in> F. \<forall>i \<in> I' \<inter> {0..<dim_row A}.  (row A i) \<bullet> x = (b $ i)"
    using subsystem_fulfills_P[of A b A' b' I' "\<lambda> p q. p \<bullet> _ = q"] C_d
    using C'_d' 
    by (metis (no_types, lifting) A A'_b' b carrier_matD(1) carrier_vecD)
  have "\<forall>x \<in> F. dim_vec x = dim_col A'" 
  proof
    fix x
    assume "x \<in> F"
    then have "x \<in> P" 
      using assms(4) face_subset_polyhedron by blast
    then have "x \<in> carrier_vec n" unfolding P_def polyhedron_def by blast
    have "dim_col A' = n" using A'_b' dim_col_subsyst_mat 
      by (metis A carrier_matD(2) fst_conv) 
    then show "dim_vec x = dim_col A'" 
      using \<open>x \<in> carrier_vec n\<close> carrier_vecD by blast
  qed
  then have "\<forall> x \<in> F. A' *\<^sub>v x \<le> b' \<and> (-A') *\<^sub>v x \<le> - b'" 
    using `\<forall> x \<in> F. A' *\<^sub>v x = b'` eq_system_is_leq_system by blast 
  then have "\<forall> x \<in> F. (A' @\<^sub>r (-A')) *\<^sub>v x = (b' @\<^sub>v (-b'))" using append_rows_le 
    by (smt (verit) \<open>\<forall>x\<in>F. A' *\<^sub>v x = b'\<close> \<open>\<forall>x\<in>F. dim_vec x = dim_col A'\<close> carrier_matI carrier_vec_dim_vec index_uminus_mat(3) mat_mult_append uminus_mult_mat_vec)

  have "dim_row C = dim_vec d" 
    using C_d(1) C_d(2) C_d(4) by blast
  have "dim_row C' = dim_vec d'" using C'_d' 
    using \<open>dim_row C = dim_vec d\<close> dims_subsyst_same' by blast
  have "{x. C' *\<^sub>v x = d' \<and> x \<in> F} = {x. A'' *\<^sub>v x = b'' \<and> x \<in> P}"
  proof(safe)
    {
      fix x
      assume "x \<in> F" "d' = C' *\<^sub>v x" 


      have "\<forall>i < dim_row C'. row C' i \<bullet> x = d' $ i" using `d' = C' *\<^sub>v x`
        by (metis index_mult_mat_vec)
      then have "\<forall>i \<in> J \<inter> {0..<dim_row C}.  (row C i) \<bullet> x = (d $ i)"
        using subsystem_fulfills_P[of C d C' d' J "\<lambda> p q. p \<bullet> x = q"] C_d
        using C'_d' by blast
      then have "\<forall>i \<in> J \<inter> {0..<dim_row A}.  (row C i) \<bullet> x = (d $ i)" 
        by (metis IntD1 IntD2 IntI \<open>dim_row A \<le> dim_row C\<close> atLeastLessThan_iff inf.absorb_iff2 inf.strict_boundedE)
      have "\<forall>i \<in> J \<inter> {0..<dim_row A}.  (row A i) \<bullet> x = (b $ i)"
        using `\<forall> i < dim_row A. (row C i) = row A i \<and> d $ i = b $ i` 
        by (metis IntD2 \<open>\<forall>i\<in>J \<inter> {0..<dim_row A}. row C i \<bullet> x = d $ i\<close> atLeastLessThan_iff)
      then have "\<forall> i < dim_row A''. (row A'' i) \<bullet> x =  (b'' $ i)" 
        using subsystem_fulfills_P'[of A b A'' b'' _ "\<lambda> p q. p \<bullet> x = q"] 
        using A A''_b'' b carrier_vecD 
        by (metis IntD1 IntD2 IntI Un_iff \<open>\<forall>x\<in>F. \<forall>i\<in>I' \<inter> {0..<dim_row A}. row A i \<bullet> x = b $ i\<close> \<open>x \<in> F\<close> carrier_matD(1))
      then show " A'' *\<^sub>v x = b''"
        using eq_for_all_index_then_eq[of A'' b'' x] `dim_row A'' = dim_vec b''` by auto
    }
    show "\<And>x.  x \<in> F \<Longrightarrow> d' = C' *\<^sub>v x \<Longrightarrow> x \<in> P" 
      using assms(4) gram_schmidt.face_subset_polyhedron by blast
    {
      fix x
      assume "x \<in> P" "b'' = A'' *\<^sub>v x" 
      then have "\<forall> i < dim_row A''. (row A'' i) \<bullet> x =  (b'' $ i)"
        by (metis index_mult_mat_vec)
      then have "\<forall>i \<in> (J \<union> I') \<inter> {0..<dim_row A}.  (row A i) \<bullet> x = (b $ i)"
        using subsystem_fulfills_P[of A b A'' b'' _ "\<lambda> p q. p \<bullet> x = q"] 
        using A A''_b'' b carrier_vecD by blast
      then have "\<forall>i \<in> J \<inter> {0..<dim_row A}.  (row C i) \<bullet> x = (d $ i)"  
        by (metis IntD1 IntD2 IntI Un_Int_eq(4) \<open>\<forall>i<dim_row A. row C i = row A i \<and> d $ i = b $ i\<close> atLeastLessThan_iff sup_commute)
      have "\<forall>i \<in> I' \<inter> {0..<dim_row A}.  (row A i) \<bullet> x = (b $ i)"  
        by (metis IntD1 IntD2 IntI Un_Int_eq(1) \<open>\<forall>i\<in>(J \<union> I') \<inter> {0..<dim_row A}. row A i \<bullet> x = b $ i\<close> sup_commute)
      then have "\<forall> i < dim_row A'. (row A' i) \<bullet> x =  (b' $ i)"
        using subsystem_fulfills_P'[of A b A' b' I' "\<lambda> p q. p \<bullet> x = q"] 
          A'_b'
        using A b carrier_vecD by blast
      then have "A' *\<^sub>v x = b'" 
        using eq_for_all_index_then_eq[of A' b' x] `dim_row A' = dim_vec b'` by auto
      have "dim_vec x = dim_col A'" 
      proof -
        have "x \<in> carrier_vec n" using `x \<in> P`unfolding P_def polyhedron_def by blast
        have "dim_col A' = n" using A'_b' dim_col_subsyst_mat 
          by (metis A carrier_matD(2) fst_conv) 
        then show "dim_vec x = dim_col A'" 
          using \<open>x \<in> carrier_vec n\<close> carrier_vecD by blast
      qed

      then have "A' *\<^sub>v x \<le> b' \<and> (-A') *\<^sub>v x \<le> - b'"
        using eq_system_is_leq_system `A' *\<^sub>v x = b'` by blast
      then have "(A' @\<^sub>r (-A')) *\<^sub>v x = (b' @\<^sub>v (-b'))"  
        by (smt (verit) \<open>A' *\<^sub>v x = b'\<close> \<open>dim_vec x = dim_col A'\<close> carrier_matI carrier_vec_dim_vec index_uminus_mat(3) mat_mult_append uminus_mult_mat_vec)
      then have "\<forall>i \<in> {dim_row A..<dim_row C}.  (row C i) \<bullet> x = (d $ i)"
        by (metis A \<open>\<forall>i\<in>{nr..<dim_row C}. row C i = row (A' @\<^sub>r - A') (i - nr) \<and> d $ i = (b' @\<^sub>v - b') $ (i - nr)\<close> \<open>dim_row C = nr + dim_row (A' @\<^sub>r - A')\<close> add.commute atLeastLessThan_iff carrier_matD(1) index_mult_mat_vec less_diff_conv2)
      then have "\<forall>i \<in> J \<inter> {0..<dim_row C}.  (row C i) \<bullet> x = (d $ i)" 
        by (metis IntD1 IntD2 IntI \<open>\<forall>i\<in>J \<inter> {0..<dim_row A}. row C i \<bullet> x = d $ i\<close> atLeastLessThan_iff le_neq_implies_less nat_le_linear)
      then have "\<forall> i < dim_row C'. (row C' i) \<bullet> x =  (d' $ i)"
        using subsystem_fulfills_P'[of C d C' d' J "\<lambda> p q. p \<bullet> x = q"] C'_d'   
        using C_d by blast
      then show " C' *\<^sub>v x = d'"
        using eq_for_all_index_then_eq[of C' d' x] `dim_row C' = dim_vec d'` by auto
      show "x \<in> F" using  A'_b' `A' *\<^sub>v x = b'` `x \<in> P` by blast
    }
  qed
  have "F' = {x. A'' *\<^sub>v x = b'' \<and> x \<in> P}" 
    using C'_d' \<open>{x. C' *\<^sub>v x = d' \<and> x \<in> F} = {x. A'' *\<^sub>v x = b'' \<and> x \<in> P}\<close> by fastforce
  then show ?thesis using char_face2[of A nr b A'' b'' "(I' \<union> J)" F'] 
    using A A''_b'' P_def assms(5) b face_non_empty by presburger
qed


lemma subsyst_with_max_ineq_is_min_face:
  fixes A :: "'a :: trivial_conjugatable_linordered_field mat"
  assumes A: "A \<in> carrier_mat nr n"
  assumes b: "b \<in> carrier_vec nr"
  defines "P \<equiv> polyhedron A b"
  assumes "((A', b') = sub_system A b I)" 
  assumes "{x. A' *\<^sub>v x = b' \<and> x \<in> P} \<noteq> {}"
  assumes "dim_vec b' = Max {dim_vec d| C d I. (C, d) = sub_system A b I \<and> 
                                                {x. C *\<^sub>v x = d \<and> x \<in> P} \<noteq> {}}"
  shows "min_face P {x. A' *\<^sub>v x = b' \<and> x \<in> P}"
proof
  show "face P {x. A' *\<^sub>v x = b' \<and> x \<in> P}" 
    using char_face2[of A nr b A' b' I "{x. A' *\<^sub>v x = b' \<and> x \<in> P}"]
    unfolding P_def 
    using A P_def assms(4) assms(5) b by blast
  show " \<not> (\<exists>F'\<subset>{x. A' *\<^sub>v x = b' \<and> x \<in> P}. face P F')" 
  proof
    assume "\<exists>F'\<subset>{x. A' *\<^sub>v x = b' \<and> x \<in> P}. face P F'" 
    obtain F' where "F'\<subset>{x. A' *\<^sub>v x = b' \<and> x \<in> P} \<and> face P F'" 
      using \<open>\<exists>F'\<subset>{x. A' *\<^sub>v x = b' \<and> x \<in> P}. face P F'\<close> by presburger
    then obtain C d I' where "((C, d) = sub_system A b I')
                              \<and> F' = {x. C *\<^sub>v x = d \<and> x \<in> P}" "(I \<inter> {0..<nr}) \<subset> (I' \<inter> {0..<nr})" 
      using obtain_I_for_subface[of A nr b A' b' I "{x. A' *\<^sub>v x = b' \<and> x \<in> P}" F']
      using A b P_def `face P {x. A' *\<^sub>v x = b' \<and> x \<in> P}` assms(4) 
      by force
    then have "dim_vec b' < dim_vec d" using less_I_less_dims_subsystem[of A nr b I I' A' b' C d]

      using A assms(4) b by blast
    have 1:"dim_vec d \<in> {dim_vec d| C d I. (C, d) = sub_system A b I \<and> 
                                                {x. C *\<^sub>v x = d \<and> x \<in> P} \<noteq> {}}" 

      by (smt (verit, best) Collect_cong \<open>(C, d) = sub_system A b I' \<and> F' = {x. C *\<^sub>v x = d \<and> x \<in> P}\<close> \<open>F' \<subset> {x. A' *\<^sub>v x = b' \<and> x \<in> P} \<and> face P F'\<close> face_non_empty mem_Collect_eq)

    have "dim_vec b = nr" using b by auto
    let ?M = "{dim_vec d| C d I. (C, d) = sub_system A b I \<and> {x. C *\<^sub>v x = d \<and> x \<in> P} \<noteq> {}}"
    have "finite ?M"
      using subset_set_of_sub_dims_finite[of ?M A b] by blast

    have "?M \<noteq> {}" using 1
      by blast
    then have "Max ?M \<in> ?M \<and> (\<forall>a \<in> ?M. a \<le> (Max ?M))"
      using eq_Max_iff[of ?M] `?M \<noteq> {}` `finite ?M` 
      by auto
    then have "dim_vec d \<le> dim_vec b'"
      using eq_Max_iff 
      using "1" assms(6) by auto
    then show False 
      using \<open>dim_vec b' < dim_vec d\<close> linorder_not_less by blast
  qed
qed

lemma obtain_min_face_polyhedron:
  fixes A :: "'a :: trivial_conjugatable_linordered_field mat"
  assumes A: "A \<in> carrier_mat nr n"
  assumes b: "b \<in> carrier_vec nr"
  defines "P \<equiv> polyhedron A b"
  assumes "P \<noteq> {}"
  obtains F where "min_face P F"
proof -
  obtain A' b' I'  where "((A', b') = sub_system A b I')" 
    "{x. A' *\<^sub>v x = b' \<and> x \<in> P} \<noteq> {}"
    "dim_vec b' = Max {dim_vec d| C d I. (C, d) = sub_system A b I \<and> 
                                                {x. C *\<^sub>v x = d \<and> x \<in> P} \<noteq> {}}"
    using  subsyst_with_max_ineq[of A nr b] assms 
    by blast 
  then have "min_face P {x. A' *\<^sub>v x = b' \<and> x \<in> P}" 
    using subsyst_with_max_ineq_is_min_face[of A nr b A' b' I'] assms by fast
  then show ?thesis 
    by (simp add: that)
qed

lemma face_contains_min_face:
  fixes A :: "'a :: trivial_conjugatable_linordered_field mat"
  assumes A: "A \<in> carrier_mat nr n"
  assumes b: "b \<in> carrier_vec nr"
  defines "P \<equiv> polyhedron A b"
  assumes "face P F" 
  shows "\<exists> F'. F' \<subseteq> F \<and> min_face P F'"
proof -
  obtain C d where C_d:"F = polyhedron C d" "dim_row C = dim_vec d" "dim_col C = n"
    using A P_def assms(4) b face_is_polyhedron by blast
  have "F \<noteq> {}" 
    using assms(4) face_non_empty by auto
  obtain F' where "min_face F F'" 
    using obtain_min_face_polyhedron[of C "dim_row C" d] C_d  
    by (metis \<open>F \<noteq> {}\<close> carrier_mat_triv carrier_vec_dim_vec) 
  have "face P F'" 
    using A P_def \<open>min_face F F'\<close> assms(4) b min_face_elim(1) face_trans by presburger
  have "\<not> (\<exists>S\<subset>F'. face F S)" 
    by (simp add: \<open>min_face F F'\<close> min_face_elim(2))
  then have "\<not> (\<exists>S\<subset>F'. face P S)" 
    by (meson \<open>min_face F F'\<close> assms(4) face_subset_polyhedron subset_is_face min_face_elim(1) psubset_imp_subset subset_trans)
  then have "min_face P F'" 
    using \<open>face P F'\<close> by blast
  then show ?thesis 
    by (meson \<open>min_face F F'\<close> face_subset_polyhedron min_face_elim(1))
qed


lemma int_all_min_faces_then_int_all_faces:
  fixes A :: "'a :: trivial_conjugatable_linordered_field mat"
  assumes A: "A \<in> carrier_mat nr n"
  assumes b: "b \<in> carrier_vec nr"
  defines "P \<equiv> polyhedron A b"
  assumes "\<forall> F. min_face P F \<longrightarrow> (\<exists> x \<in> F. x \<in> \<int>\<^sub>v)"
  shows "\<forall> F. face P F \<longrightarrow> (\<exists> x \<in> F. x \<in> \<int>\<^sub>v)"
proof
  fix F

  show "face P F \<longrightarrow> (\<exists>x\<in>F. x \<in> \<int>\<^sub>v)" 
  proof 
    assume "face P F" 
    then obtain F' where "F' \<subseteq> F \<and> min_face P F'" using face_contains_min_face assms by metis
    then show "\<exists> x \<in> F. x \<in> \<int>\<^sub>v" 
      by (meson assms(4) subset_iff)
  qed
qed

lemma int_all_faces_then_int_all_min_faces:
  fixes A :: "'a :: trivial_conjugatable_linordered_field mat"
  assumes A: "A \<in> carrier_mat nr n"
  assumes b: "b \<in> carrier_vec nr"
  defines "P \<equiv> polyhedron A b"
  assumes "\<forall> F. face P F \<longrightarrow> (\<exists> x \<in> F. x \<in> \<int>\<^sub>v)"
  shows "\<forall> F. min_face P F \<longrightarrow> (\<exists> x \<in> F. x \<in> \<int>\<^sub>v)" 
  using assms(4) min_face_elim(1) 
  by presburger


lemma int_all_min_faces_iff_int_all_faces:
  fixes A :: "'a :: trivial_conjugatable_linordered_field mat"
  assumes A: "A \<in> carrier_mat nr n"
  assumes b: "b \<in> carrier_vec nr"
  defines "P \<equiv> polyhedron A b"
  shows "(\<forall> F. min_face P F \<longrightarrow> (\<exists> x \<in> F. x \<in> \<int>\<^sub>v)) \<longleftrightarrow> (\<forall> F. face P F \<longrightarrow> (\<exists> x \<in> F. x \<in> \<int>\<^sub>v))"
  using int_all_min_faces_then_int_all_faces[of A nr b]
    int_all_faces_then_int_all_min_faces[of A nr b]  assms 
  by blast

text \<open>a ==> b\<close>

lemma lin_comb_in_hyp:
  fixes y :: "'a :: trivial_conjugatable_linordered_field vec"
  assumes "P \<subseteq> carrier_vec n" 
  assumes "y \<in> P"
  assumes "z \<in> P"
  assumes "support_hyp P \<alpha> \<beta>" 
  assumes "\<beta> = \<alpha> \<bullet> (l \<cdot>\<^sub>v y + (1 - l) \<cdot>\<^sub>v z)"
  assumes "l > 0 \<and> l < 1" 
  shows "\<alpha> \<bullet> y = \<beta>" 
proof -
  have "\<alpha> \<in> carrier_vec n" using assms(4) unfolding support_hyp_def by auto
  have " \<beta> = \<alpha> \<bullet> (l \<cdot>\<^sub>v y) + \<alpha> \<bullet> ((1 - l) \<cdot>\<^sub>v z)" 
    using scalar_prod_add_distrib[of \<alpha> n "l \<cdot>\<^sub>v y" "(1 - l) \<cdot>\<^sub>v z"] `\<alpha> \<in> carrier_vec n`
      assms(1-3) assms(5) by blast

  then have 1: "l * (\<alpha> \<bullet> y) + (1 - l) * (\<alpha> \<bullet> z) = \<beta>" 
    using \<open>\<alpha> \<in> carrier_vec n\<close> assms(1-3) in_mono by fastforce

  have "\<alpha> \<bullet> y \<le> \<beta>" 
    using assms(2) assms(4) support_hyp_is_valid(1) valid_ineq_elim(1) by blast
  have "\<alpha> \<bullet> z \<le> \<beta>" 
    using assms(3) assms(4) support_hyp_is_valid(1) valid_ineq_elim(1) by blast 
  show "\<alpha> \<bullet> y = \<beta>" 
  proof(cases "\<alpha> \<bullet> z = \<beta>")
    case True
    then show ?thesis 
      using  assms(6) 1 
      by (simp add: left_diff_distrib)
  next
    case False
    have "\<alpha> \<bullet> z < \<beta>" 
      by (simp add: False \<open>\<alpha> \<bullet> z \<le> \<beta>\<close> order.strict_iff_order)
    then have "(1 - l) * (\<alpha> \<bullet> z) < (1 - l) * \<beta>" using assms(6) 
      by auto
    have "l * (\<alpha> \<bullet> y) \<le> l * \<beta>" 
      by (simp add: \<open>0 < l \<and> l < 1\<close> \<open>\<alpha> \<bullet> y \<le> \<beta>\<close>)
    then have "l * (\<alpha> \<bullet> y) + (1 - l) * (\<alpha> \<bullet> z) < l * \<beta> + (1 - l) * \<beta>" 
      using \<open>(1 - l) * (\<alpha> \<bullet> z) < (1 - l) * \<beta>\<close> add_mono_thms_linordered_field(4) by blast
    then have "l * (\<alpha> \<bullet> y) + (1 - l) * (\<alpha> \<bullet> z) < \<beta>" by algebra
    then show ?thesis using 1 by blast  
  qed
qed


lemma P_int_then_face_int:
  fixes A :: "'a :: trivial_conjugatable_linordered_field mat"
  assumes A: "A \<in> carrier_mat nr n"
  assumes b: "b \<in> carrier_vec nr"
  defines "P \<equiv> polyhedron A b"
  assumes "P = integer_hull P" 
  shows "(\<forall> F. face P F \<longrightarrow> (\<exists> x \<in> F. x \<in> \<int>\<^sub>v))" 
proof
  fix F
  show " face P F \<longrightarrow> (\<exists>x\<in>F. x \<in> \<int>\<^sub>v)"
  proof 
    assume "face P F"
    obtain x where "x \<in> F" 
      using \<open>face P F\<close> face_non_empty by fastforce
    show "\<exists>x\<in>F. x \<in> \<int>\<^sub>v" 
    proof(cases "x \<in> \<int>\<^sub>v")
      case True
      then show ?thesis using `x \<in> F` 
        by blast
    next
      case False
      obtain \<alpha> \<beta>  where \<alpha>_\<beta>:"P \<noteq> {} \<and>  F = P \<inter> {x |x. \<alpha> \<bullet> x = \<beta>} \<and> support_hyp P \<alpha> \<beta> " 
        using \<open>face P F\<close> face_def by auto
      obtain y z l where lin_comb_x:"y \<in> P \<inter> \<int>\<^sub>v" "z \<in> P" "x = l \<cdot>\<^sub>v y + (1 - l) \<cdot>\<^sub>v z" "l > 0 \<and> l < 1"
        using elem_of_P_is_lin_comb[of P x] 
        using P_def assms(4) gram_schmidt.polyhedron_def False \<open>x \<in> F\<close> 
        using \<open>face P F\<close> face_subset_polyhedron by blast 
      have "P \<subseteq> carrier_vec n" unfolding P_def polyhedron_def by auto
      have "\<alpha> \<bullet> y = \<beta>" 
        using lin_comb_in_hyp[of P y z \<alpha> \<beta> l] 
          \<alpha>_\<beta> lin_comb_x `P \<subseteq> carrier_vec n` \<open>x \<in> F\<close> by fastforce
      then have "y \<in> F" using `y \<in> P \<inter> \<int>\<^sub>v`  \<alpha>_\<beta> by blast
      then show ?thesis 
        using \<open>y \<in> P \<inter> \<int>\<^sub>v\<close> by blast
    qed
  qed
qed

text\<open>b \<Longrightarrow> f\<close>

lemma int_face_then_max_suphyp_int:
  fixes A :: "'a :: trivial_conjugatable_linordered_field mat"
  assumes A: "A \<in> carrier_mat nr n"
  assumes b: "b \<in> carrier_vec nr"
  defines "P \<equiv> polyhedron A b"
  assumes "(\<forall> F. face P F \<longrightarrow> (\<exists> x \<in> F. x \<in> \<int>\<^sub>v))" 
  shows "\<forall> \<alpha> \<in> carrier_vec n. has_Maximum { \<alpha> \<bullet> x | x. x \<in> P} \<longrightarrow>
   (\<exists>x. x \<in> P \<and> \<alpha> \<bullet> x = Maximum { \<alpha> \<bullet> x | x. x \<in> P}  \<and> x \<in> \<int>\<^sub>v)"
proof(safe)
  fix \<alpha> :: "'a vec"
  assume "\<alpha> \<in> carrier_vec n" "has_Maximum {\<alpha> \<bullet> x |x. x \<in> P}"
  let ?\<beta> = "Maximum { \<alpha> \<bullet> x | x. x \<in> P}" 

  have "?\<beta> \<in>  { \<alpha> \<bullet> x | x. x \<in> P}" 
   apply(rule has_MaximumD \<open>has_Maximum {\<alpha> \<bullet> x |x. x \<in> P}\<close>) 
    by (simp add: \<open>has_Maximum {\<alpha> \<bullet> x |x. x \<in> P}\<close>)
  have "support_hyp P \<alpha> ?\<beta>" unfolding support_hyp_def 
    using \<open>\<alpha> \<in> carrier_vec n\<close> \<open>has_Maximum {\<alpha> \<bullet> x |x. x \<in> P}\<close> by blast
  have "face P (P \<inter> {y |y. \<alpha> \<bullet> y = ?\<beta>})"
    unfolding face_def
    apply(auto)
    using \<open>Maximum {\<alpha> \<bullet> x |x. x \<in> P} \<in> {\<alpha> \<bullet> x |x. x \<in> P}\<close> apply blast
    using \<open>support_hyp P \<alpha> (Maximum {\<alpha> \<bullet> x |x. x \<in> P})\<close> by blast
  then show "\<exists>x. x \<in> P \<and> \<alpha> \<bullet> x = Maximum { \<alpha> \<bullet> x | x. x \<in> P}  \<and> x \<in> \<int>\<^sub>v" using assms(4)
    by blast
qed


text \<open>f ==> a\<close>

lemma int_hull_subset:
  fixes A :: "'a :: trivial_conjugatable_linordered_field mat"
  assumes A: "A \<in> carrier_mat nr n"
  assumes b: "b \<in> carrier_vec nr"
 defines "P \<equiv> polyhedron A b"
 shows "integer_hull P \<subseteq> P"
  by (metis A Int_subset_iff P_def b convex_def convex_hull_mono 
      integer_hull_def order_refl polyhedra_are_convex)

lemma pugi:
 fixes A :: "'a :: trivial_conjugatable_linordered_field mat"
  assumes A: "A \<in> carrier_mat nr n"
  assumes b: "b \<in> carrier_vec nr"
  defines "P \<equiv> polyhedron A b"
  assumes "y \<in> P - integer_hull P"
  shows "y \<notin> \<int>\<^sub>v"
proof
  assume " y \<in> \<int>\<^sub>v"
  then have "y \<in> P \<inter>  \<int>\<^sub>v" using assms(4) by auto
  have "P \<inter> \<int>\<^sub>v \<subseteq> carrier_vec n" using P_def unfolding polyhedron_def 
    by blast
  then have "y \<in> integer_hull P" 
    unfolding integer_hull_def using set_in_convex_hull[of "P \<inter> \<int>\<^sub>v"] 
    using \<open>y \<in> P \<inter> \<int>\<^sub>v\<close> by blast
  then show False using assms(4) 
    by blast
qed


lemma pgrej:
 fixes A :: "'a :: trivial_conjugatable_linordered_field mat"
  assumes A: "A \<in> carrier_mat nr n"
  assumes b: "b \<in> carrier_vec nr"
  defines "P \<equiv> polyhedron A b"
  assumes "y \<notin> P"
  assumes "y \<in> carrier_vec n"
  shows "\<exists>j. j < nr \<and> (row A j) \<bullet> y >  b $ j"
proof(rule ccontr)
  assume "\<not> (\<exists>j<nr. b $ j < row A j \<bullet> y)"
  then have 1: "\<forall>j<dim_row A.  row A j \<bullet> y \<le> b $ j" 
    by (metis A carrier_matD(1) leI)
  have 2: "dim_row A = dim_vec b" 
    using A b carrier_vecD by blast
  have "A *\<^sub>v y \<le> b" using leq_for_all_index_then_eq 1 2 
    by blast
  have "y \<in> P"  
    unfolding P_def polyhedron_def 
    using \<open>A *\<^sub>v y \<le> b\<close> assms(5) by blast
  then show False 
    by (simp add: assms(4))
qed


lemma fgwegwe:
    fixes A :: "'a  mat"
  fixes b:: "'a vec" 
  assumes A: "A \<in> carrier_mat nr n"
  assumes b: "b \<in> carrier_vec nr"
  defines "P \<equiv> polyhedron A b"
  assumes "i < nr"
  assumes "P \<noteq> {}" 
  shows "has_Maximum { row A i \<bullet> x | x. x \<in> P}"
proof -
  have "\<forall> x \<in> P. row A i \<bullet> x \<le> b $ i" 
    using P_def unfolding polyhedron_def 
  mult_mat_vec_def 
    apply  (auto simp:  less_eq_vec_def) 
    using assms(4) b by force
  then have "valid_ineq P (row A i) (b $ i)" unfolding valid_ineq_def 
    using A assms(4) row_carrier_vec by blast
  then show ?thesis using face_non_empty1
    using A Collect_cong P_def assms(5) b by auto
qed


end

context gram_schmidt_floor
begin

definition floor\<^sub>v where
  "floor\<^sub>v v = vec (dim_vec v) (\<lambda> i. floor (v $ i))"

definition ceil\<^sub>v where
  "ceil\<^sub>v v = vec (dim_vec v) (\<lambda> i. ceiling (v $ i))"

lemma grg:
  fixes x ::"'a" 
  assumes "x \<notin> \<int>" 
  shows "floor x + 1 = ceiling x" unfolding ceiling_def 
proof -
  have "\<lfloor>x\<rfloor> + 1 + \<lfloor>- x\<rfloor> = 0"
  oops

lemma floor_vec_plus_one:
  fixes v:: "'a vec"
  shows "floor\<^sub>v v + 1\<^sub>v (dim_vec v) = ceil\<^sub>v v"
  unfolding floor\<^sub>v_def ceil\<^sub>v_def one_vec_def ceiling_def oops

 
lemma integer_hull_is_integer_hull:
  assumes "P \<subseteq> carrier_vec n"
  shows "integer_hull (integer_hull P) = integer_hull P" 
  unfolding integer_hull_def 
  by (smt (verit, del_insts) Int_iff assms convex_hull_mono convex_hulls_are_convex 
gram_schmidt.convex_def set_in_convex_hull subset_antisym subset_eq)

lemma gojeg:
  fixes bound :: "'a " 
  assumes A: "A \<in> carrier_mat nr nc" 
    and c: "c \<in> carrier_vec nc"
    and sat: "\<exists> x \<in> carrier_vec nc. A *\<^sub>v x \<le> 0\<^sub>v nr" 
    and bounded: "\<forall> x \<in> carrier_vec nc. A *\<^sub>v x \<le> 0\<^sub>v nr \<longrightarrow> c \<bullet> x \<le> bound" 
  shows "Maximum {c \<bullet> x | x. x \<in> carrier_vec nc \<and> A *\<^sub>v x \<le> 0\<^sub>v nr}
       = Minimum {0\<^sub>v nr  \<bullet> y | y. y \<ge> 0\<^sub>v nr \<and> A\<^sup>T *\<^sub>v y = c}"
    and "has_Maximum {c \<bullet> x | x. x \<in> carrier_vec nc \<and> A *\<^sub>v x \<le> 0\<^sub>v nr}" 
    and "has_Minimum {0\<^sub>v nr \<bullet> y | y. y \<ge> 0\<^sub>v nr \<and> A\<^sup>T *\<^sub>v y = c}" 
  using strong_duality_theorem_primal_sat_bounded_min_max[of A nr nc "0\<^sub>v nr" c bound] assms
  using zero_carrier_vec  apply blast
  using A \<open>\<lbrakk>A \<in> carrier_mat nr nc; 0\<^sub>v nr \<in> carrier_vec nr; c \<in> carrier_vec nc; \<exists>x\<in>carrier_vec nc. A *\<^sub>v x \<le> 0\<^sub>v nr; \<forall>x\<in>carrier_vec nc. A *\<^sub>v x \<le> 0\<^sub>v nr \<longrightarrow> c \<bullet> x \<le> bound\<rbrakk> \<Longrightarrow> has_Maximum {c \<bullet> x |x. x \<in> carrier_vec nc \<and> A *\<^sub>v x \<le> 0\<^sub>v nr}\<close> bounded c sat zero_carrier_vec apply blast
  using A \<open>\<lbrakk>A \<in> carrier_mat nr nc; 0\<^sub>v nr \<in> carrier_vec nr; c \<in> carrier_vec nc; \<exists>x\<in>carrier_vec nc. A *\<^sub>v x \<le> 0\<^sub>v nr; \<forall>x\<in>carrier_vec nc. A *\<^sub>v x \<le> 0\<^sub>v nr \<longrightarrow> c \<bullet> x \<le> bound\<rbrakk> \<Longrightarrow> has_Minimum {0\<^sub>v nr \<bullet> y |y. 0\<^sub>v nr \<le> y \<and> A\<^sup>T *\<^sub>v y = c}\<close> bounded c sat zero_carrier_vec by blast

lemma gojeg2:
  fixes bound :: "'a " 
  assumes A: "A \<in> carrier_mat nr nc" 
    and c: "c \<in> carrier_vec nc"
    and sat: "\<exists> x \<in> carrier_vec nc. A *\<^sub>v x \<le> 0\<^sub>v nr" 
    and bounded: "\<forall> x \<in> carrier_vec nc. A *\<^sub>v x \<le> 0\<^sub>v nr \<longrightarrow> c \<bullet> x \<le> bound" 
  shows "Maximum {c \<bullet> x | x. x \<in> carrier_vec nc \<and> A *\<^sub>v x \<le> 0\<^sub>v nr} = 0"
proof -
  have  "Maximum {c \<bullet> x | x. x \<in> carrier_vec nc \<and> A *\<^sub>v x \<le> 0\<^sub>v nr}
       = Minimum {0\<^sub>v nr  \<bullet> y | y. y \<ge> 0\<^sub>v nr \<and> A\<^sup>T *\<^sub>v y = c}"
    and "has_Maximum {c \<bullet> x | x. x \<in> carrier_vec nc \<and> A *\<^sub>v x \<le> 0\<^sub>v nr}" 
    and "has_Minimum {0\<^sub>v nr \<bullet> y | y. y \<ge> 0\<^sub>v nr \<and> A\<^sup>T *\<^sub>v y = c}" 
    using gojeg assms  apply  blast
    using gojeg(2) assms  apply  blast
    using gojeg(3) assms  by  blast
  then obtain y where "y \<ge> 0\<^sub>v nr \<and> A\<^sup>T *\<^sub>v y = c \<and> 0\<^sub>v nr \<bullet> y = Minimum {0\<^sub>v nr  \<bullet> y | y. y \<ge> 0\<^sub>v nr \<and> A\<^sup>T *\<^sub>v y = c}"
    using has_MinimumD(1) by fastforce
  then have "y \<in> carrier_vec nr" 
    by (metis carrier_dim_vec index_zero_vec(2) less_eq_vec_def)

  then have "0\<^sub>v nr \<bullet> y = 0" unfolding scalar_prod_def 
    by simp
  then show ?thesis 
    using \<open>0\<^sub>v nr \<le> y \<and> A\<^sup>T *\<^sub>v y = c \<and> 0\<^sub>v nr \<bullet> y = Minimum {0\<^sub>v nr \<bullet> y |y. 0\<^sub>v nr \<le> y \<and> A\<^sup>T *\<^sub>v y = c}\<close> \<open>Maximum {c \<bullet> x |x. x \<in> carrier_vec nc \<and> A *\<^sub>v x \<le> 0\<^sub>v nr} = Minimum {0\<^sub>v nr \<bullet> y |y. 0\<^sub>v nr \<le> y \<and> A\<^sup>T *\<^sub>v y = c}\<close> by presburger
qed


lemma utye:
   fixes A :: "'a  mat"
  fixes b:: "'a vec" 
  assumes A: "A \<in> carrier_mat nr n"
  assumes b: "b \<in> carrier_vec nr"
  defines "P \<equiv> polyhedron A b"
  assumes "P \<noteq> {}" 
  assumes "has_Maximum {c \<bullet> x | x. x \<in> P}" 
  assumes "x \<in> P \<and> c \<bullet> x = Maximum {c \<bullet> x | x. x \<in> P}"
  obtains F here where "min_face P F \<and> x \<in> F" 
  oops

lemma fgweugugwe:
   fixes A :: "'a  mat"
  fixes b:: "'a vec" 
  assumes A: "A \<in> carrier_mat nr n"
  assumes b: "b \<in> carrier_vec nr"
  defines "P \<equiv> polyhedron A b"
  assumes "P \<noteq> {}"
  assumes "integer_hull P = polyhedron C d"
  assumes "j < dim_row C" 
  assumes "dim_col C = n"
  assumes "has_Maximum { row C j \<bullet> x | x. x \<in> polyhedron C d}"
assumes "\<forall> \<alpha> \<in> carrier_vec n. has_Maximum { \<alpha> \<bullet> x | x. x \<in> P} \<longrightarrow>
   (\<exists>x. x \<in> P \<and> \<alpha> \<bullet> x = Maximum { \<alpha> \<bullet> x | x. x \<in> P}  \<and> x \<in> \<int>\<^sub>v)"
  shows "has_Maximum { row C j \<bullet> x | x. x \<in> P}"
proof(rule ccontr)
  assume "\<not> has_Maximum {row C j \<bullet> x |x. x \<in> P}" 
  then have "\<not> (\<exists> x. x \<in> {row C j \<bullet> x |x. x \<in> P} \<and> (\<forall> y \<in> {row C j \<bullet> x |x. x \<in> P}. y \<le> x))" 
    unfolding has_Maximum_def 
    by blast
  then have "\<forall>x \<in> {row C j \<bullet> x |x. x \<in> P}. \<not> (\<forall> y \<in> {row C j \<bullet> x |x. x \<in> P}. y \<le> x)" 
    by blast
  then have "\<forall>x \<in> {row C j \<bullet> x |x. x \<in> P}. (\<exists> y \<in> {row C j \<bullet> x |x. x \<in> P}. y > x)" 
    by fastforce
  then have "\<forall>x \<in> P. \<exists> y \<in> P. row C j \<bullet> y > row C j \<bullet> x" 
    by auto
  have "\<forall> v. \<exists> x \<in> P. row C j \<bullet> x \<ge> v"
  proof(rule ccontr)
    assume "\<not> (\<forall>v. \<exists>x\<in>P. v \<le> row C j \<bullet> x)"
    then obtain Bnd where "\<forall> y \<in> P. row C j \<bullet> y < Bnd" 
      by (meson less_le_not_le linorder_linear)
    then have "\<forall> x \<in> carrier_vec n. A *\<^sub>v x \<le> b \<longrightarrow> row C j \<bullet> x \<le> Bnd"
      unfolding P_def polyhedron_def 
      using order_le_less by auto
    then have "has_Maximum {row C j \<bullet> x | x. x \<in> carrier_vec n \<and> A *\<^sub>v x \<le> b}"
      using 
        strong_duality_theorem_primal_sat_bounded_min_max[of A nr n b "row C j" Bnd] 
      by (metis (no_types, lifting) A Collect_empty_eq P_def 
            assms(4) assms(7) b polyhedron_def row_carrier)
    then show False using `\<not> has_Maximum {row C j \<bullet> x |x. x \<in> P}`
      unfolding P_def polyhedron_def 
      by fastforce
  qed
  then have "\<forall>v. \<exists>x\<in>carrier_vec n. A *\<^sub>v x \<le> b \<and> v \<le> row C j \<bullet> x" 
    unfolding P_def polyhedron_def 
    by auto
  then have "\<not> (\<exists> y. y \<ge> 0\<^sub>v nr \<and> A\<^sup>T *\<^sub>v y = row C j)" 
        using unbounded_primal_solutions[of A nr n b "row C j"] A b 
        using assms(7) row_carrier by blast
 then have "\<not>  (\<forall> y. y \<in> carrier_vec n \<longrightarrow> A *\<^sub>v y \<ge> 0\<^sub>v nr \<longrightarrow> y \<bullet> row C j \<ge> 0)"
    using Farkas_Lemma[of "A\<^sup>T" nr "row C j"] using assms(7) row_carrier A
    by force
then obtain y where "y \<in> carrier_vec n \<and> A *\<^sub>v y \<ge> 0\<^sub>v nr \<and> y \<bullet> row C j < 0" 
    using leI by blast

  let ?y' = " (1/Max (abs ` (vec_set y))) \<cdot>\<^sub>v y" 
  let ?app_rows = "mat_of_rows n [1\<^sub>v n, (-1\<^sub>v n)]"
  let ?app_vec = "vec_of_list [of_int n, of_int n]"
  let ?full_A = "- A @\<^sub>r ?app_rows"
  let ?full_b = "0\<^sub>v nr @\<^sub>v ?app_vec"
  let ?c = "row C j"
  let ?P' = "polyhedron ?full_A ?full_b"


  have "?full_A \<in> carrier_mat (nr+2) n" sorry
  have "?full_b \<in> carrier_vec (nr+2)" sorry

  have "?y' \<le> 1\<^sub>v n" sorry
  have "?y' \<ge> - 1\<^sub>v n" sorry
  have "(- 1\<^sub>v n) \<bullet> y \<le> of_int n" sorry
  have "(1\<^sub>v n) \<bullet> y \<le> of_int n" sorry

  have 1:"polyhedron ?full_A ?full_b \<noteq> {}" sorry
 have "\<exists> x \<in> carrier_vec n. ?full_A *\<^sub>v x \<le> ?full_b" sorry
  have "\<exists> bnd. \<forall> x \<in> carrier_vec n. ?full_A *\<^sub>v x \<le> ?full_b \<longrightarrow> ?c \<bullet> x \<le> bnd" sorry
  then have "has_Maximum {?c \<bullet> x | x. x \<in> carrier_vec n \<and> ?full_A *\<^sub>v x \<le> ?full_b}"
    using strong_duality_theorem_primal_sat_bounded_min_max[of ?full_A "nr+2" n ?full_b ?c]
    using \<open>- A @\<^sub>r mat_of_rows n [1\<^sub>v n, - 1\<^sub>v n] \<in> carrier_mat (nr + 2) n\<close> \<open>0\<^sub>v nr @\<^sub>v vec_of_list [of_int (int n), of_int (int n)] \<in> carrier_vec (nr + 2)\<close> \<open>\<exists>x\<in>carrier_vec n. (- A @\<^sub>r mat_of_rows n [1\<^sub>v n, - 1\<^sub>v n]) *\<^sub>v x \<le> 0\<^sub>v nr @\<^sub>v vec_of_list [of_int (int n), of_int (int n)]\<close> assms(7) row_carrier by blast

  then obtain \<beta> where "\<beta> = Maximum {?c \<bullet> x | x. x \<in> carrier_vec n \<and> ?full_A *\<^sub>v x \<le> ?full_b}"
    by auto
  then have 2:"support_hyp ?P' ?c \<beta>" unfolding support_hyp_def  
    by (smt (verit, best) Collect_cong \<open>has_Maximum {row C j \<bullet> x |x. x \<in> carrier_vec n \<and> (- A @\<^sub>r mat_of_rows n [1\<^sub>v n, - 1\<^sub>v n]) *\<^sub>v x \<le> 0\<^sub>v nr @\<^sub>v vec_of_list [of_int (int n), of_int (int n)]}\<close> assms(7) mem_Collect_eq polyhedron_def row_carrier)
  have "\<beta> > 0" sorry
  let ?F = " ?P' \<inter> {x |x. ?c \<bullet> x = \<beta>}"
  have "face ?P' ?F" unfolding face_def using 1 2 
    by blast 
  then obtain F where F_def:"min_face ?P' F \<and> F \<subseteq> ?F" 
    by (meson \<open>- A @\<^sub>r mat_of_rows n [1\<^sub>v n, - 1\<^sub>v n] \<in> carrier_mat (nr + 2) n\<close> \<open>0\<^sub>v nr @\<^sub>v vec_of_list [of_int (int n), of_int (int n)] \<in> carrier_vec (nr + 2)\<close> gram_schmidt.face_contains_min_face)

  then obtain z where "z \<in> F" 
    by (metis ex_in_conv face_non_empty gram_schmidt.min_face_elim(1))
   obtain A' b' I where " F \<subseteq> ?P' \<and> F \<noteq> {} \<and>
            F = {x. x \<in> carrier_vec n \<and> A' *\<^sub>v x = b'} \<and>
                (A', b') = sub_system ?full_A ?full_b I" 
     using F_def
    by (smt (verit, best) \<open>- A @\<^sub>r mat_of_rows n [1\<^sub>v n, - 1\<^sub>v n] \<in> carrier_mat (nr + 2) n\<close> \<open>0\<^sub>v nr @\<^sub>v vec_of_list [of_int (int n), of_int (int n)] \<in> carrier_vec (nr + 2)\<close> char_min_face)

  then have "A' *\<^sub>v z = b'" 
    using \<open>z \<in> F\<close> by force
  have "A' \<in> \<int>\<^sub>m" sorry
  have "b' \<in> \<int>\<^sub>v" sorry
  obtain k z' where  " z' = k \<cdot>\<^sub>v z \<and> z' \<in> \<int>\<^sub>v" using `A' *\<^sub>v z = b'` `A' \<in> \<int>\<^sub>m` `b' \<in> \<int>\<^sub>v`
    sorry
  have "A *\<^sub>v z' \<le> 0\<^sub>v nr" sorry

  obtain v where "v \<in> P \<and> v \<in> \<int>\<^sub>v" sorry
  then have "v \<in> integer_hull P" sorry
  have "\<forall> m. v + of_int m \<cdot>\<^sub>v z' \<in> P \<and> v + of_int m \<cdot>\<^sub>v z' \<in> \<int>\<^sub>v" sorry
  then have "\<forall> m. v + of_int m \<cdot>\<^sub>v z' \<in> integer_hull P" sorry



  oops

  then have "valid_ineq ?P' ?c \<beta>" 
    using support_hyp_is_valid(1) by blast





  oops

  then obtain F where "min_face (polyhedron ?full_A ?full_b) F" 
    by (meson \<open>- A @\<^sub>r mat_of_rows n [1\<^sub>v n, - 1\<^sub>v n] \<in> carrier_mat (nr + 2) n\<close> \<open>0\<^sub>v nr @\<^sub>v vec_of_list [of_int (int n), of_int (int n)] \<in> carrier_vec (nr + 2)\<close> obtain_min_face_polyhedron)
  then obtain A' b' I where " F \<subseteq> ?P' \<and> F \<noteq> {} \<and>
            F = {x. x \<in> carrier_vec n \<and> A' *\<^sub>v x = b'} \<and>
                (A', b') = sub_system ?full_A ?full_b I" 
    by (smt (verit, best) \<open>- A @\<^sub>r mat_of_rows n [1\<^sub>v n, - 1\<^sub>v n] \<in> carrier_mat (nr + 2) n\<close> \<open>0\<^sub>v nr @\<^sub>v vec_of_list [of_int (int n), of_int (int n)] \<in> carrier_vec (nr + 2)\<close> char_min_face)

    oops

 
      oops
  then have "\<not>  (\<forall> y. y \<in> carrier_vec n \<longrightarrow> A *\<^sub>v y \<ge> 0\<^sub>v nr \<longrightarrow> y \<bullet> row C j \<ge> 0)"
    using Farkas_Lemma[of "A\<^sup>T" nr "row C j"] using assms(7) row_carrier A
    by force
  then obtain y where "y \<in> carrier_vec n \<and> A *\<^sub>v y \<ge> 0\<^sub>v nr \<and> y \<bullet> row C j < 0" 
    using leI by blast

  have "\<not>  (\<forall> y. y \<in> carrier_vec n \<and> y \<in> \<int>\<^sub>v \<longrightarrow> A *\<^sub>v y \<ge> 0\<^sub>v nr \<longrightarrow> y \<bullet> row C j \<ge> 0)" 
  proof
    assume "\<forall>y. y \<in> carrier_vec n \<and> y \<in> \<int>\<^sub>v \<longrightarrow> 0\<^sub>v nr \<le> A *\<^sub>v y \<longrightarrow> 0 \<le> y \<bullet> row C j"


    oops
  then obtain y' where "y' \<in> carrier_vec n \<and> y' \<in> \<int>\<^sub>v \<and> A *\<^sub>v y' \<ge> 0\<^sub>v nr \<and> y' \<bullet> row C j < 0" 
    using leI by blast
  obtain m where "m \<in>  \<int>\<^sub>v \<and> m \<in> P" sorry
  then have "m \<in> integer_hull P" sorry
  


    oops
    by blast
  then have "y \<in> \<int>\<^sub>v" sledgehammer
  then have "row C j \<bullet> y \<ge> 0" unfolding mult_mat_vec_def 
  oops


lemma pugi:
  fixes A :: "'a  mat"
  fixes b:: "'a vec" 
  assumes A: "A \<in> carrier_mat nr n"
  assumes b: "b \<in> carrier_vec nr"
   and AI: "A \<in> \<int>\<^sub>m"
  and bI: "b \<in> \<int>\<^sub>v"
defines "P \<equiv> polyhedron A b"
assumes "\<forall> \<alpha> \<in> carrier_vec n. has_Maximum { \<alpha> \<bullet> x | x. x \<in> P} \<longrightarrow>
   (\<exists>x. x \<in> P \<and> \<alpha> \<bullet> x = Maximum { \<alpha> \<bullet> x | x. x \<in> P}  \<and> x \<in> \<int>\<^sub>v)"
shows "P = integer_hull P" 
proof(cases "P = {}")
  case True
  then show ?thesis 
    by (metis A P_def b int_hull_subset subset_empty)
next
  case False

  obtain C d nr' where C_d:"C \<in> carrier_mat nr' n \<and> d \<in> carrier_vec nr' \<and> integer_hull P = polyhedron C d"
    using gram_schmidt_floor.integer_hull_of_polyhedron[of A nr n b P] assms 
    by blast
  have "\<exists> Bnd. Bnd =  Max (abs ` (elements_mat A \<union> vec_set b))" 
    by blast
  have "integer_hull P \<noteq> {}"
  proof(rule ccontr)
    assume "\<not> integer_hull P \<noteq> {}"
    then have "convex_hull (P \<inter> \<int>\<^sub>v) = {}" unfolding integer_hull_def  
      by argo
    then have "P \<inter> \<int>\<^sub>v = {}" using set_in_convex_hull 
      by (metis A Diff_empty P_def \<open>\<not> integer_hull P \<noteq> {}\<close> b disjoint_iff_not_equal pugi)
    have "nr > 0"
    proof(rule ccontr)
      assume "\<not> 0 < nr"
      then have "nr = 0" by auto
      then have "\<forall> x. A *\<^sub>v x \<le> b" 
        by (metis A b carrier_matD(1) carrier_vecD leq_for_all_index_then_eq less_nat_zero_code)
      then have "P = carrier_vec n " unfolding P_def polyhedron_def 
        by fast 
      have "0\<^sub>v n \<in> \<int>\<^sub>v" 
        using zero_vec_is_int by blast
      then show False using `P \<inter> \<int>\<^sub>v = {}` 
        using \<open>P = carrier_vec n\<close> by blast
    qed

    then obtain i where "i < nr" by auto
    then have "has_Maximum { row A i \<bullet> x | x. x \<in> P}" using fgwegwe 
      using A False P_def b by blast
    then have "\<exists>x. x \<in> P \<and> row A i \<bullet> x = Maximum { row A i \<bullet> x | x. x \<in> P}  \<and> x \<in> \<int>\<^sub>v" using assms(6)
      by (meson A \<open>i < nr\<close> row_carrier_vec)
    then show False 
      using \<open>P \<inter> \<int>\<^sub>v = {}\<close> by blast
  qed

  show ?thesis
  proof(rule ccontr)

    assume"P\<noteq> integer_hull P"
    then obtain y where y: "y \<in> P - integer_hull P" 
      by (metis A Diff_iff P_def b int_hull_subset set_eq_subset subset_iff)
    then have "y \<in> carrier_vec n" unfolding P_def polyhedron_def 
      by blast
    have " y \<notin> polyhedron C d" using C_d y 
      by blast                                                 
    then obtain j where "j<nr' \<and> row C j \<bullet> y > d $ j" using y pgrej[of C nr' d y] C_d  
          `y \<in> carrier_vec n` 
      by blast
    let ?\<alpha> = "row C j"
    let ?\<beta> = "d $ j"
    have " has_Maximum { ?\<alpha> \<bullet> x | x. x \<in> polyhedron C d}" 
using fgwegwe[of C nr' d j] `integer_hull P \<noteq> {}` 
  using C_d \<open>j < nr' \<and> d $ j < row C j \<bullet> y\<close> by blast
    have "?\<alpha> \<in> carrier_vec n" 
      by (meson C_d \<open>j < nr' \<and> d $ j < row C j \<bullet> y\<close> row_carrier_vec)
    have " has_Maximum { ?\<alpha> \<bullet> x | x. x \<in> P}" sorry
    then obtain x where "x \<in> P \<and> ?\<alpha> \<bullet> x = Maximum { ?\<alpha> \<bullet> x | x. x \<in> P}  \<and> x \<in> \<int>\<^sub>v" 
      using assms(6)  
      by (meson \<open>row C j \<in> carrier_vec n\<close>) 
    then have "?\<alpha> \<bullet> y \<le> ?\<alpha> \<bullet> x" 
      using \<open>has_Maximum {row C j \<bullet> x |x. x \<in> P}\<close> has_MaximumD(2) y by fastforce
    have "x \<in> integer_hull P" unfolding integer_hull_def 
      by (metis (no_types, lifting) A Diff_iff P_def \<open>x \<in> P \<and> row C j \<bullet> x = Maximum {row C j \<bullet> x |x. x \<in> P} \<and> x \<in> \<int>\<^sub>v\<close> b integer_hull_def pugi)
    then have "?\<alpha> \<bullet> x \<le> d $ j" sorry
    then have "?\<alpha> \<bullet> y \<le> d $ j" 
      using \<open>row C j \<bullet> y \<le> row C j \<bullet> x\<close> by linarith
    then show False 
      using \<open>j < nr' \<and> d $ j < row C j \<bullet> y\<close> linorder_not_le by blast
  qed
qed



end
end