theory Integer_Polyhedron
  imports Faces
   Well_Quasi_Orders.Minimal_Elements
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
  then have "dim_row A' = card (I \<inter> {0..<nr})" using I_subsys_same_card
  by (metis (mono_tags, lifting) A assms(4) b carrier_matD(1) carrier_vecD dims_subsyst_same' inf.cobounded2 snd_conv)

have "sub_system A b J = sub_system A b (J \<inter> {0..<nr})"
    using same_subsyst_I_intersect_rows A b 
    by blast
  then have "dim_row C = card (J \<inter> {0..<nr})" using I_subsys_same_card
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
  by (metis A append_rows_nth(2) assms(2) carrier_matD(1))
   
      

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

  
end
end