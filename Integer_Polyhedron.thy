theory Integer_Polyhedron
  imports Faces
   Well_Quasi_Orders.Minimal_Elements
  Linear_Inequalities.Integer_Hull
  Missing_Sums 
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


lemma fwqfqwf:
  fixes x :: "'a :: trivial_conjugatable_linordered_field vec"
  assumes "P \<subseteq> carrier_vec n"
  assumes "P = integer_hull P"
  assumes "finite Ws"
  assumes "Ws \<subseteq> P \<inter> \<int>\<^sub>v"  
  assumes "x \<notin> \<int>\<^sub>v"
  assumes "convex_lincomb c' Ws x"
  obtains y z l where "y \<in> P \<inter> \<int>\<^sub>v" "z \<in> P" "x = l \<cdot>\<^sub>v y + (1 - l) \<cdot>\<^sub>v z" "l > 0 \<and> l \<le> 1"
proof -
  have "Ws \<subseteq> carrier_vec n" using assms by blast

    have "x \<in> convex_hull Ws" 
      using assms convex_hull_def by blast

    obtain Wsl c where Wc: "convex_lincomb_list c Wsl x \<and> c 0 \<noteq> 0 \<and> Ws = set Wsl"
    proof -
obtain Wsl where "set Wsl =  Ws " using assms
      by (meson finite_list) 

    
    then have "convex_hull Ws = convex_hull_list Wsl" 
      using finite_convex_hull_iff_convex_hull_list 
      using \<open>set Wsl = Ws\<close> `Ws \<subseteq> carrier_vec n` by force
    have "x \<in> convex_hull Ws" 
      using assms convex_hull_def by blast
    then have "x \<in> convex_hull_list Wsl" 
      by (simp add: \<open>convex_hull Ws = convex_hull_list Wsl\<close>)
    then obtain c where c:"convex_lincomb_list c Wsl x" 
      using gram_schmidt.convex_hull_list_def by fastforce

    have "\<exists> i < length Wsl. c i \<noteq> 0" using assms(5) 
      using \<open>convex_lincomb_list c Wsl x\<close> class_field.zero_not_one convex_lincomb_list_def finsum_zero'
      by (metis atLeastLessThan_iff)
    then obtain i where "i < length Wsl \<and> c i \<noteq> 0" by blast
    have "Ws = set (Wsl[0:= Wsl ! i, i:=Wsl ! 0])"
      by (metis \<open>i < length Wsl \<and> c i \<noteq> 0\<close> \<open>set Wsl = Ws\<close> length_pos_if_in_set nth_mem set_swap)
    have "convex_hull_list Wsl = convex_hull_list (Wsl[0:= Wsl ! i, i:=Wsl ! 0])"
      using convex_hull_list_mono 
      by (metis \<open>Ws = set (Wsl[0 := Wsl ! i, i := Wsl ! 0])\<close> \<open>Ws \<subseteq> carrier_vec n\<close> \<open>set Wsl = Ws\<close> convex_hull_list_eq_set)
 
    let ?Wsl' = "Wsl[0:= Wsl ! i, i:=Wsl ! 0]" 
    let ?c' = "c(0:= c i, i:= c 0)"

    have cll:"(lincomb_list c Wsl = x \<and> (\<forall>i<length Wsl. 0 \<le> c i)) \<and> sum c {0..<length Wsl} = 1" 
      using c unfolding convex_lincomb_list_def nonneg_lincomb_list_def by auto
    have "sumlist (map (\<lambda>ia. c ia \<cdot>\<^sub>v Wsl ! ia) [0..<length Wsl]) = x" using cll
      unfolding lincomb_list_def by auto


    have "(\<lambda>ia. c ia \<cdot>\<^sub>v Wsl ! ia)(0 := c i \<cdot>\<^sub>v Wsl ! i, i := c 0 \<cdot>\<^sub>v Wsl ! 0) = 
(\<lambda>ia. (c(0 := c i, i := c 0)) ia \<cdot>\<^sub>v Wsl[0 := Wsl ! i, i := Wsl ! 0] ! ia)" 
      apply auto
      apply rule+
      
      using \<open>i < length Wsl \<and> c i \<noteq> 0\<close> length_pos_if_in_set nth_mem apply fastforce
  by (smt (verit) \<open>i < length Wsl \<and> c i \<noteq> 0\<close> fun_upd_apply length_list_update not_less_zero nth_list_update zero_less_iff_neq_zero)

  then have "map (\<lambda>ia. (c(0 := c i, i := c 0)) ia \<cdot>\<^sub>v Wsl[0 := Wsl ! i, i := Wsl ! 0] ! ia)
      [0..<length (Wsl[0 := Wsl ! i, i := Wsl ! 0])] =
  (map (\<lambda>ia. c ia \<cdot>\<^sub>v Wsl ! ia) [0..<length Wsl])
      [0:= (map (\<lambda>ia. c ia \<cdot>\<^sub>v Wsl ! ia) [0..<length Wsl]) ! i, 
      i := (map (\<lambda>ia. c ia \<cdot>\<^sub>v Wsl ! ia) [0..<length Wsl]) ! 0]"
    using nmdo[of 0 Wsl i "(\<lambda>ia. c ia \<cdot>\<^sub>v Wsl ! ia)"] 
    by (metis \<open>i < length Wsl \<and> c i \<noteq> 0\<close> less_nat_zero_code  neq0_conv)
  have "set (map (\<lambda>ia. c ia \<cdot>\<^sub>v Wsl ! ia) [0..<length Wsl]) \<subseteq> carrier_vec n"
  proof
    fix z
    assume "z \<in> set (map (\<lambda>ia. c ia \<cdot>\<^sub>v Wsl ! ia) [0..<length Wsl])"
    then obtain j where "j <length Wsl \<and> z = c j \<cdot>\<^sub>v Wsl ! j" 
      by auto
    then show "z \<in> carrier_vec n" 
    using `Ws \<subseteq> carrier_vec n` `set Wsl = Ws` 
    using nth_mem by blast
qed

  then have " M.sumlist
      (map (\<lambda>ia. (c(0 := c i, i := c 0)) ia \<cdot>\<^sub>v Wsl[0 := Wsl ! i, i := Wsl ! 0] ! ia)
        [0..<length (Wsl[0 := Wsl ! i, i := Wsl ! 0])]) =
      sumlist (map (\<lambda>ia. c ia \<cdot>\<^sub>v Wsl ! ia) [0..<length Wsl])" 
    using sumlist_swap_upd_same[of "(map (\<lambda>ia. c ia \<cdot>\<^sub>v Wsl ! ia) [0..<length Wsl])" 0 i] 
    by (metis \<open>i < length Wsl \<and> c i \<noteq> 0\<close> \<open>map (\<lambda>ia. (c(0 := c i, i := c 0)) ia \<cdot>\<^sub>v Wsl[0 := Wsl ! i, i := Wsl ! 0] ! ia) [0..<length (Wsl[0 := Wsl ! i, i := Wsl ! 0])] = (map (\<lambda>ia. c ia \<cdot>\<^sub>v Wsl ! ia) [0..<length Wsl]) [0 := map (\<lambda>ia. c ia \<cdot>\<^sub>v Wsl ! ia) [0..<length Wsl] ! i, i := map (\<lambda>ia. c ia \<cdot>\<^sub>v Wsl ! ia) [0..<length Wsl] ! 0]\<close> length_map less_nat_zero_code map_nth neq0_conv)

    have " M.sumlist
      (map (\<lambda>ia. (c(0 := c i, i := c 0)) ia \<cdot>\<^sub>v Wsl[0 := Wsl ! i, i := Wsl ! 0] ! ia)
        [0..<length (Wsl[0 := Wsl ! i, i := Wsl ! 0])]) =
     x" 
      using \<open>M.sumlist (map (\<lambda>ia. (c(0 := c i, i := c 0)) ia \<cdot>\<^sub>v Wsl[0 := Wsl ! i, i := Wsl ! 0] ! ia) [0..<length (Wsl[0 := Wsl ! i, i := Wsl ! 0])]) = M.sumlist (map (\<lambda>ia. c ia \<cdot>\<^sub>v Wsl ! ia) [0..<length Wsl])\<close> \<open>M.sumlist (map (\<lambda>ia. c ia \<cdot>\<^sub>v Wsl ! ia) [0..<length Wsl]) = x\<close> by blast
    have "(\<forall>ia<length (Wsl[0 := Wsl ! i, i := Wsl ! 0]). 0 \<le> (c(0 := c i, i := c 0)) ia)"
      using swap_fun_nonneg[of 0 Wsl i ]  
      by (metis \<open>i < length Wsl \<and> c i \<noteq> 0\<close> cll length_list_update less_nat_zero_code neq0_conv)

    then have "convex_lincomb_list ?c' ?Wsl' x" 
      unfolding convex_lincomb_list_def  nonneg_lincomb_list_def lincomb_list_def
using jkkhhhjl
      by (metis (mono_tags, lifting) \<open>M.sumlist (map (\<lambda>ia. (c(0 := c i, i := c 0)) ia \<cdot>\<^sub>v Wsl[0 := Wsl ! i, i := Wsl ! 0] ! ia) [0..<length (Wsl[0 := Wsl ! i, i := Wsl ! 0])]) = x\<close> \<open>i < length Wsl \<and> c i \<noteq> 0\<close> \<open>set Wsl = Ws\<close> assms(3) cll length_pos_if_in_set nth_mem)

    then show ?thesis 
      by (metis \<open>Ws = set (Wsl[0 := Wsl ! i, i := Wsl ! 0])\<close> \<open>i < length Wsl \<and> c i \<noteq> 0\<close> fun_upd_other fun_upd_same that)
    qed
    have "convex_hull Ws = convex_hull_list Wsl" 
      using finite_convex_hull_iff_convex_hull_list 
      using Wc 
      using \<open>Ws \<subseteq> carrier_vec n\<close> by presburger 
    have "x \<in> convex_hull Ws" 
      using assms convex_hull_def by blast
    then have "x \<in> convex_hull_list Wsl" 
      by (simp add: \<open>convex_hull Ws = convex_hull_list Wsl\<close>)

  
    then have "lincomb_list c Wsl = x \<and> (\<forall> i < length Wsl. c i \<ge> 0) \<and> sum c {0..<length Wsl} = 1"
      using convex_lincomb_list_def nonneg_lincomb_list_def Wc by blast
    have "lincomb_list c Wsl = sumlist (map (\<lambda>i. c i \<cdot>\<^sub>v Wsl ! i) [0..<length Wsl])"
      by (simp add: lincomb_list_def)
    have "Ws \<noteq> {}" 
      using \<open>x \<in> convex_hull Ws\<close> convex_hull_empty(2) by blast
    have "Wsl \<noteq> []" 
      using \<open>Ws \<noteq> {}\<close> Wc by blast
    have "set Wsl \<subseteq> carrier_vec n" 
      using \<open>Ws \<subseteq> carrier_vec n\<close> Wc by auto
    have "sum c {0..<length Wsl} = 1" 
      using \<open>lincomb_list c Wsl = x \<and> (\<forall>i<length Wsl. 0 \<le> c i) \<and> sum c {0..<length Wsl} = 1\<close> by blast

    obtain a ax where "Wsl = a # ax" 
      by (meson \<open>Wsl \<noteq> []\<close> neq_Nil_conv)

  have "0 # [1..<length (a # ax)] = [0..<length (a # ax)]"
            using ff 
            by blast 
  
 then have "map (\<lambda>i. c i \<cdot>\<^sub>v (a # ax) ! i) [0..<length (a #ax)] = 
       (\<lambda>i. c i \<cdot>\<^sub>v (a # ax) ! i) 0 # map (\<lambda>i. c i \<cdot>\<^sub>v (a # ax) ! i) [1..<length (a # ax)]"
   using List.list.map(2)[of "(\<lambda>i. c i \<cdot>\<^sub>v (a # ax) ! i)" 0 "[1..<length (a # ax)]"] by argo
  then have "sumlist (map (\<lambda>i. c i \<cdot>\<^sub>v (a # ax) ! i) [0..<length (a #ax)]) =
       (\<lambda>i. c i \<cdot>\<^sub>v (a # ax) ! i) 0 + sumlist ( map (\<lambda>i. c i \<cdot>\<^sub>v (a # ax) ! i) [1..<length (a # ax)])"
    using M.sumlist_Cons by presburger
  then have "(\<lambda>i. c i \<cdot>\<^sub>v (a # ax) ! i) 0 + sumlist ( map (\<lambda>i. c i \<cdot>\<^sub>v (a # ax) ! i) [1..<length (a # ax)]) =
      c 0 \<cdot>\<^sub>v a + sumlist ( map (\<lambda>i. c i \<cdot>\<^sub>v (a # ax) ! i) [1..<length (a # ax)])"
    by force
  have "set Wsl \<subseteq> \<int>\<^sub>v" using assms(4) 
    by (simp add: Wc)
  have "set Wsl \<subseteq> carrier_vec n" 
    using \<open>set Wsl \<subseteq> carrier_vec n\<close> by auto
  then have " \<forall>i<length Wsl. c i < 1" using bnter[of c Wsl x] using Wc assms(4-5) 
    using \<open>set Wsl \<subseteq> \<int>\<^sub>v\<close> by presburger
  then have "c 0 \<noteq> 1" 
    by (metis \<open>Wsl \<noteq> []\<close> length_greater_0_conv less_numeral_extra(4))
  let ?f = "(\<lambda>i. c (i + 1) / (1 - c 0))" 
  have "sum ?f {0..<length ax} = 1" 
  proof -
    have "length (a # ax) = 1 + length ax" 
      by simp
    then have "sum (\<lambda>i. c (i + 1)) {0..<length ax} = sum (\<lambda>i. c i) {1..<length (a # ax)}"
      by (metis Nat.add_0_right  add.commute sum.shift_bounds_nat_ivl)
    then have "(1/(1 - c 0)) * sum (\<lambda>i. c (i + 1)) {0..<length ax} =
              (1/(1 - c 0)) * sum (\<lambda>i. c i) {1..<length (a # ax)}" by simp
    have "sum ?f {0..<length ax} = (1/(1 - c 0)) * sum (\<lambda>i. c (i + 1)) {0..<length ax}" 
      using mult_hom.hom_sum[of "(1/(1 - c 0))" "(\<lambda>i. c (i + 1))" "{0..<length ax}"]
      by simp
    then have "c 0 + sum c {1..<length Wsl} = sum c {0..<length Wsl}" 
      by (metis \<open>Wsl = a # ax\<close> \<open>length (a # ax) = 1 + length ax\<close> add.commute sum_range_divided_at_zero)
    then have "c 0 + sum c {1..<length (a#ax)} = 1" 
      by (metis \<open>Wsl = a # ax\<close> \<open>sum c {0..<length Wsl} = 1\<close>)
    then have "sum (\<lambda>i. c (i + 1)) {0..<length ax} = 1 - c 0" 
      using \<open>(\<Sum>i = 0..<length ax. c (i + 1)) = sum c {1..<length (a # ax)}\<close> by linarith 
    then have "(1/(1 - c 0)) * (1 - c 0) =  1" using `c 0 \<noteq> 1` 
      by (metis nonzero_eq_divide_eq r_right_minus_eq)
    then show ?thesis 
      using \<open>(\<Sum>i = 0..<length ax. c (i + 1) / (1 - c 0)) = 1 / (1 - c 0) * (\<Sum>i = 0..<length ax. c (i + 1))\<close> \<open>(\<Sum>i = 0..<length ax. c (i + 1)) = 1 - c 0\<close> by presburger
  qed


  have "\<forall>i \<in>  set [1..<length (a # ax)].  c i \<cdot>\<^sub>v (a # ax) ! i \<in> carrier_vec n" 
  proof 
    fix i
    assume "i \<in>  set [1..<length (a # ax)]" 
    then have "i < length (a # ax)" 
      by (metis atLeastLessThan_iff set_upt)
    then have "(a # ax) ! i \<in> set (a # ax)" 
      using nth_mem by blast
    then show "c i \<cdot>\<^sub>v (a # ax) ! i \<in> carrier_vec n" 
      using \<open>Wsl = a # ax\<close> \<open>set Wsl \<subseteq> carrier_vec n\<close> by blast
  qed

  then have "(\<lambda>i. c i \<cdot>\<^sub>v (a # ax) ! i) \<in> set [1..<length (a # ax)] \<rightarrow> carrier_vec n" 
    by blast
  then have " M.sumlist (map (\<lambda>i. c i \<cdot>\<^sub>v (a # ax) ! i) [1..<length (a # ax)]) =
    (1 - c 0) \<cdot>\<^sub>v M.sumlist (map (\<lambda>i. 1 / (1 - c 0) \<cdot>\<^sub>v (c i \<cdot>\<^sub>v (a # ax) ! i)) [1..<length (a # ax)])"
    using sumlist_map_mult[of "(\<lambda>i. c i \<cdot>\<^sub>v (a # ax) ! i)" " [1..<length (a # ax)]" "(1 - c 0)"] `c 0 \<noteq> 1` 
    by linarith
  have "(\<lambda>i. 1 / (1 - c 0) \<cdot>\<^sub>v (c i \<cdot>\<^sub>v (a # ax) ! i)) =  (\<lambda>i. (c i / (1 - c 0)) \<cdot>\<^sub>v (a # ax) ! i)"
    using `c 0 \<noteq> 1` 
    by fastforce  

  then have "sumlist ( map (\<lambda>i. c i \<cdot>\<^sub>v (a # ax) ! i) [1..<length (a # ax)]) = 
    (1 - c 0) \<cdot>\<^sub>v sumlist ( map (\<lambda>i. (c i / (1 - c 0)) \<cdot>\<^sub>v (a # ax) ! i) [1..<length (a # ax)])" 
   
   using \<open>M.sumlist (map (\<lambda>i. c i \<cdot>\<^sub>v (a # ax) ! i) [1..<length (a # ax)]) = (1 - c 0) \<cdot>\<^sub>v M.sumlist (map (\<lambda>i. 1 / (1 - c 0) \<cdot>\<^sub>v (c i \<cdot>\<^sub>v (a # ax) ! i)) [1..<length (a # ax)])\<close> by presburger

  have "sumlist ( map (\<lambda>i. (c i / (1 - c 0)) \<cdot>\<^sub>v (a # ax) ! i) [1..<length (a # ax)]) = 
      sumlist ( map (\<lambda>i. (c (i + 1) / (1 - c 0)) \<cdot>\<^sub>v ax ! i) [0..<length ax])" 
using aghjk[of "\<lambda>i. (c i / (1 - c 0))" a ax]
  by argo
  have "finite (set ax)" 
    by auto
  have "set ax \<subseteq> set Wsl" 
    using \<open>Wsl = a # ax\<close> by auto
  then have "set ax \<subseteq> carrier_vec n" using `set Wsl \<subseteq> carrier_vec n`  
    by blast
  have " set ax \<subseteq> P \<inter> \<int>\<^sub>v" 
    using Wc \<open>set ax \<subseteq> set Wsl\<close> assms(4) by blast
  have "(\<forall> i < length Wsl. c i \<ge> 0)" 
    using \<open>lincomb_list c Wsl = x \<and> (\<forall>i<length Wsl. 0 \<le> c i) \<and> sum c {0..<length Wsl} = 1\<close> by presburger
  have "(1 - c 0) > 0" using mvdryy
    by (metis \<open>c 0 \<noteq> 1\<close> \<open>lincomb_list c Wsl = x \<and> (\<forall>i<length Wsl. 0 \<le> c i) \<and> sum c {0..<length Wsl} = 1\<close> atLeastLessThan_empty bot_nat_0.extremum_unique diff_ge_0_iff_ge empty_iff gr_zeroI not_one_le_zero order_le_imp_less_or_eq r_right_minus_eq sum_nonpos) 
  
  then have " \<forall>i<length ax. 0 \<le> c (i + 1) / (1 - c 0)"  
    by (simp add: \<open>Wsl = a # ax\<close> \<open>\<forall>i<length Wsl. 0 \<le> c i\<close>)
  have 1:"sumlist ( map (\<lambda>i. (c (i + 1) / (1 - c 0)) \<cdot>\<^sub>v ax ! i) [0..<length ax]) \<in> P" 
    using lincomb_in_integer_set[of ax P ?f] `sum ?f {0..<length ax} = 1`  
    using \<open>\<forall>i<length ax. 0 \<le> c (i + 1) / (1 - c 0)\<close> \<open>set ax \<subseteq> P \<inter> \<int>\<^sub>v\<close> \<open>set ax \<subseteq> carrier_vec n\<close> assms(2)
    unfolding lincomb_list_def 
    by blast
  have 2:"x = c 0 \<cdot>\<^sub>v a + (1 - c 0) \<cdot>\<^sub>v sumlist ( map (\<lambda>i. (c (i + 1) / (1 - c 0)) \<cdot>\<^sub>v ax ! i) [0..<length ax])" 
    using \<open>M.sumlist (map (\<lambda>i. c i / (1 - c 0) \<cdot>\<^sub>v (a # ax) ! i) [1..<length (a # ax)]) = M.sumlist (map (\<lambda>i. c (i + 1) / (1 - c 0) \<cdot>\<^sub>v ax ! i) [0..<length ax])\<close> \<open>M.sumlist (map (\<lambda>i. c i \<cdot>\<^sub>v (a # ax) ! i) [0..<length (a # ax)]) = c 0 \<cdot>\<^sub>v (a # ax) ! 0 + M.sumlist (map (\<lambda>i. c i \<cdot>\<^sub>v (a # ax) ! i) [1..<length (a # ax)])\<close> \<open>M.sumlist (map (\<lambda>i. c i \<cdot>\<^sub>v (a # ax) ! i) [1..<length (a # ax)]) = (1 - c 0) \<cdot>\<^sub>v M.sumlist (map (\<lambda>i. c i / (1 - c 0) \<cdot>\<^sub>v (a # ax) ! i) [1..<length (a # ax)])\<close> \<open>Wsl = a # ax\<close> \<open>c 0 \<cdot>\<^sub>v (a # ax) ! 0 + M.sumlist (map (\<lambda>i. c i \<cdot>\<^sub>v (a # ax) ! i) [1..<length (a # ax)]) = c 0 \<cdot>\<^sub>v a + M.sumlist (map (\<lambda>i. c i \<cdot>\<^sub>v (a # ax) ! i) [1..<length (a # ax)])\<close> \<open>lincomb_list c Wsl = M.sumlist (map (\<lambda>i. c i \<cdot>\<^sub>v Wsl ! i) [0..<length Wsl])\<close> \<open>lincomb_list c Wsl = x \<and> (\<forall>i<length Wsl. 0 \<le> c i) \<and> sum c {0..<length Wsl} = 1\<close> by presburger
  have 3:"a \<in> P \<inter> \<int>\<^sub>v" 
    using \<open>Wsl = a # ax\<close> Wc assms(4) by force
  have 4:"c 0 \<ge> 0" 
    by (simp add: \<open>Wsl = a # ax\<close> \<open>lincomb_list c Wsl = x \<and> (\<forall>i<length Wsl. 0 \<le> c i) \<and> sum c {0..<length Wsl} = 1\<close>)
  have 5:"c 0 \<le> 1" using member_le_sum[of 0 "{0..<length Wsl}" c] 
    using \<open>Wsl = a # ax\<close> \<open>lincomb_list c Wsl = x \<and> (\<forall>i<length Wsl. 0 \<le> c i) \<and> sum c {0..<length Wsl} = 1\<close> by force
  
  have "c 0 \<noteq> 0" 
    by (simp add: Wc)
  then show ?thesis using 1 2 3 4 5
    using that 
    by auto 
qed


lemma P_int_then_face_int:
   fixes A :: "'a :: trivial_conjugatable_linordered_field mat"
 assumes A: "A \<in> carrier_mat nr n"
 assumes b: "b \<in> carrier_vec nr"
 defines "P \<equiv> polyhedron A b"
 assumes "P = integer_hull P" 
 shows "(\<forall> F. face P F \<longrightarrow> (\<exists> x \<in> F. x \<in> \<int>\<^sub>v))" 
proof(rule) 
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

    obtain \<alpha> \<beta>  where "P \<noteq> {} \<and>  F = P \<inter> {x |x. \<alpha> \<bullet> x = \<beta>} \<and> support_hyp P \<alpha> \<beta> " 
      using \<open>face P F\<close> face_def by auto

  then obtain Ws c' where  "finite Ws \<and> Ws \<subseteq> P \<inter> \<int>\<^sub>v \<and> convex_lincomb c' Ws x"
      using assms(4) unfolding integer_hull_def
      by (smt (verit, ccfv_SIG) IntD1 \<open>x \<in> F\<close> gram_schmidt.convex_hull_def mem_Collect_eq)
    then obtain y z l where "y \<in> P \<inter> \<int>\<^sub>v" "z \<in> P" "x = l \<cdot>\<^sub>v y + (1 - l) \<cdot>\<^sub>v z" "l > 0 \<and> l \<le> 1"
      using fwqfqwf[of P Ws x c'] 
      using P_def assms(4) gram_schmidt.polyhedron_def False by blast
    have "\<alpha> \<bullet> (l \<cdot>\<^sub>v y + (1 - l) \<cdot>\<^sub>v z) = \<beta>" 
      using \<open>P \<noteq> {} \<and> F = P \<inter> {x |x. \<alpha> \<bullet> x = \<beta>} \<and> support_hyp P \<alpha> \<beta>\<close> \<open>x = l \<cdot>\<^sub>v y + (1 - l) \<cdot>\<^sub>v z\<close> \<open>x \<in> F\<close> by fastforce
    then have "\<alpha> \<bullet> (l \<cdot>\<^sub>v y) + \<alpha> \<bullet> ((1 - l) \<cdot>\<^sub>v z) = \<beta>" 
      using scalar_prod_add_distrib[of \<alpha> n "l \<cdot>\<^sub>v y" "(1 - l) \<cdot>\<^sub>v z"] 
      by (metis (no_types, lifting) IntE P_def \<open>P \<noteq> {} \<and> F = P \<inter> {x |x. \<alpha> \<bullet> x = \<beta>} \<and> support_hyp P \<alpha> \<beta>\<close> \<open>y \<in> P \<inter> \<int>\<^sub>v\<close> \<open>z \<in> P\<close> gram_schmidt.polyhedron_def mem_Collect_eq smult_closed support_hyp_elim(3))
    then have 1: "l * (\<alpha> \<bullet> y) + (1 - l) * (\<alpha> \<bullet> z) = \<beta>" 
      by (metis (no_types, lifting) IntE P_def \<open>P \<noteq> {} \<and> F = P \<inter> {x |x. \<alpha> \<bullet> x = \<beta>} \<and> support_hyp P \<alpha> \<beta>\<close> \<open>y \<in> P \<inter> \<int>\<^sub>v\<close> \<open>z \<in> P\<close> gram_schmidt.polyhedron_def mem_Collect_eq scalar_prod_smult_distrib support_hyp_elim(3))
    have "\<alpha> \<bullet> y \<le> \<beta>" using `y \<in> P \<inter> \<int>\<^sub>v` 
      by (meson IntD1 \<open>P \<noteq> {} \<and> F = P \<inter> {x |x. \<alpha> \<bullet> x = \<beta>} \<and> support_hyp P \<alpha> \<beta>\<close> support_hyp_is_valid(1) valid_ineq_def)
    have "\<alpha> \<bullet> z \<le> \<beta>" using `z \<in> P` 
          by (meson  \<open>P \<noteq> {} \<and> F = P \<inter> {x |x. \<alpha> \<bullet> x = \<beta>} \<and> support_hyp P \<alpha> \<beta>\<close> support_hyp_is_valid(1) valid_ineq_def)
        have "l \<noteq> 0" using `l > 0 \<and> l \<le> 1` by blast 

        show "\<exists>x\<in>F. x \<in> \<int>\<^sub>v" 
        proof(cases "l = 1")
          case True
          have "x = 1 \<cdot>\<^sub>v y + 0 \<cdot>\<^sub>v z" using `x = l \<cdot>\<^sub>v y + (1 - l) \<cdot>\<^sub>v z` True by algebra
          then have "x = 1 \<cdot>\<^sub>v y" 
            by (metis (no_types, lifting) IntD1 P_def True \<open>0 < l \<and> l \<le> 1\<close> \<open>y \<in> P \<inter> \<int>\<^sub>v\<close> \<open>z \<in> P\<close> add_smult_distrib_vec diff_numeral_special(9) gram_schmidt.polyhedron_def le_add_diff_inverse mem_Collect_eq smult_l_null)
          then have "x = y" 
            by simp

          then show ?thesis 
            using \<open>x \<in> F\<close> \<open>y \<in> P \<inter> \<int>\<^sub>v\<close> by blast
        next
          case False
          have "l < 1" using False  `l > 0 \<and> l \<le> 1` by linarith  
    have "\<alpha> \<bullet> y = \<beta>" 
    proof(cases "\<alpha> \<bullet> z = \<beta>")
      case True
      have "l * (\<alpha> \<bullet> y) + (1 - l) * \<beta> = \<beta>" using 1 True by argo
      then have "l * (\<alpha> \<bullet> y) = \<beta> - (1 - l) * \<beta>" by auto
      then have "l * (\<alpha> \<bullet> y) = l * \<beta>" by algebra
      then show ?thesis using `l \<noteq> 0` 
        using mult_cancel_left by blast
    next
      case False
      have "\<alpha> \<bullet> z < \<beta>" 
        by (simp add: False \<open>\<alpha> \<bullet> z \<le> \<beta>\<close> order.strict_iff_order)
      then have "(1 - l) * (\<alpha> \<bullet> z) < (1 - l) * \<beta>" using `l < 1` 
        by auto
      have "l * (\<alpha> \<bullet> y) \<le> l * \<beta>" 
        by (simp add: \<open>0 < l \<and> l \<le> 1\<close> \<open>\<alpha> \<bullet> y \<le> \<beta>\<close>)
      then have "l * (\<alpha> \<bullet> y) + (1 - l) * (\<alpha> \<bullet> z) < l * \<beta> + (1 - l) * \<beta>" 
        using \<open>(1 - l) * (\<alpha> \<bullet> z) < (1 - l) * \<beta>\<close> add_mono_thms_linordered_field(4) by blast
      then have "l * (\<alpha> \<bullet> y) + (1 - l) * (\<alpha> \<bullet> z) < \<beta>" by algebra
      
      then show ?thesis using `l * (\<alpha> \<bullet> y) + (1 - l) * (\<alpha> \<bullet> z) = \<beta>` by blast  
    qed
    then have "y \<in> F" using `y \<in> P \<inter> \<int>\<^sub>v` 
      using \<open>P \<noteq> {} \<and> F = P \<inter> {x |x. \<alpha> \<bullet> x = \<beta>} \<and> support_hyp P \<alpha> \<beta>\<close> by blast
    then show ?thesis 
      using \<open>y \<in> P \<inter> \<int>\<^sub>v\<close> by blast
  qed
qed
qed
qed
  
end
end