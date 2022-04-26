theory Integer_hull_f_to_a
  imports Faces
    Well_Quasi_Orders.Minimal_Elements
    Linear_Inequalities.Integer_Hull
    Linear_Inequalities.Farkas_Lemma
    Integer_Polyhedron
    Missing_Sums 
    "HOL.Rat"

begin

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

lemma vnvnvn:
  fixes A :: "'a  mat"
  assumes A: "A \<in> carrier_mat nr n"
  assumes b: "b \<in> carrier_vec nr"
  defines "P \<equiv> polyhedron A b"
  assumes "min_face P F"
  obtains A' b' I'  where "((A', b') = sub_system A b I')" 
    " F = {x. x \<in> carrier_vec n \<and> A' *\<^sub>v x = b'}"
    "dim_vec b' = Min {dim_vec d| C d I. (C, d) = sub_system A b I \<and> 
                                             F = {x. x \<in> carrier_vec n \<and> C *\<^sub>v x = d}}"
proof-
  have "dim_vec b = nr" using b by auto
  let ?M = "{dim_vec d| C d I. (C, d) = sub_system A b I \<and>  F = {x. x \<in> carrier_vec n \<and> C *\<^sub>v x = d}}"
  have "finite ?M"
    using subset_set_of_sub_dims_finite[of ?M A b] by blast
  have "finite ?M" using subset_set_of_sub_dims_finite[of ?M A b] by blast
  obtain A' b' I where " F \<subseteq> P \<and> F \<noteq> {} \<and>
            F = {x. x \<in> carrier_vec n \<and> A' *\<^sub>v x = b'} \<and> (A', b') = sub_system A b I"
    using char_min_face 
    using A P_def assms(4) b by auto
  then have "dim_vec b' \<in> ?M" by auto
  then have "?M \<noteq> {}"  
    by blast
  then have "Min ?M \<in> ?M \<and> (\<forall>a \<in> ?M. a \<ge> (Min ?M))"
    using eq_Min_iff[of ?M] `?M \<noteq> {}` `finite ?M` 
    by auto
  then show ?thesis 
    using that by force
qed



lemma fffppp:
  assumes "i1 = pick I j1"
  assumes "i2 = pick I j2"
  assumes "(A', b') = sub_system A b I"
  assumes "j1 < dim_row A'"
  assumes "j2 < dim_row A'" 
  assumes "j1 \<noteq> j2"
  shows "i1 \<noteq> i2" 
proof(cases "infinite I")
  case True
  then show ?thesis 
    using assms(1) assms(2) assms(6) pick_eq_iff_inf by blast
next
  case False
  then show ?thesis using dim_row_less_card_I[of I A b] 
    by (metis assms(1) assms(2) assms(3) assms(4) assms(5) assms(6) fst_conv 
        not_less_iff_gr_or_eq order_less_le_trans pick_mono_le)
qed



lemma vnvnvnoo:
  fixes A :: "'a  mat"
  assumes A: "A \<in> carrier_mat nr n"
  assumes b: "b \<in> carrier_vec nr"
  defines "P \<equiv> polyhedron A b"
  assumes "P \<noteq> {}"
  assumes "min_face P F"
  assumes "dim_vec b' = Min {dim_vec d | C d I'.  F = {x. x \<in> carrier_vec n \<and> C *\<^sub>v x = d} \<and> 
          (C, d) = sub_system A b I'}"
  assumes " F = {x. x \<in> carrier_vec n \<and> A' *\<^sub>v x = b'}"  
  assumes "(A', b') = sub_system A b I"
  shows "distinct (rows A')" 
proof(rule ccontr)
  assume "\<not> distinct (rows A') "
  then obtain j1 j2 where j1j2: "j1 \<noteq> j2 \<and> j1 < dim_row A' \<and> j2 < dim_row A' \<and> row A' j1 = row A' j2" 
    by (metis distinct_conv_nth length_rows nth_rows)
  obtain i1 where i1:"i1 < dim_row A \<and> i1 \<in> I \<and> row A i1 = row A' j1 \<and> i1 = (pick I j1) \<and> b' $ j1 = b $ i1" 
    using exist_index_in_A[of A b j1 I] 
    by (metis A \<open>j1 \<noteq> j2 \<and> j1 < dim_row A' \<and> j2 < dim_row A' \<and> row A' j1 = row A' j2\<close> assms(8) b carrier_matD(1) carrier_vecD dims_subsyst_same' fst_conv snd_conv)

  obtain i2 where i2: "i2 < dim_row A \<and> i2 \<in> I \<and> row A i2 = row A' j2 \<and> i2 = (pick I j2) \<and> b' $ j2 = b $ i2" 
    using exist_index_in_A[of A b j2 I] 

    by (metis A \<open>j1 \<noteq> j2 \<and> j1 < dim_row A' \<and> j2 < dim_row A' \<and> row A' j1 = row A' j2\<close> assms(8) b carrier_matD(1) carrier_vecD dims_subsyst_same' fst_conv snd_conv)

  then have "i1 \<noteq> i2" using fffppp[of i1 I j1 i2 j2 A' b' A b] 
    using i1 \<open>j1 \<noteq> j2 \<and> j1 < dim_row A' \<and> j2 < dim_row A' \<and> row A' j1 = row A' j2\<close> assms(8) by presburger

  have " b $ i1 =  b $ i2" 
  proof(rule ccontr)
    assume "b $ i1 \<noteq> b $ i2"
    then have "b' $ j1 \<noteq> b' $ j2" using i1 i2 by auto
    obtain x where "x \<in> F" 
      by (metis A P_def assms(5) b equals0I gram_schmidt.char_min_face)
    then have "x \<in> carrier_vec n \<and> A' *\<^sub>v x = b'" 
      using assms(7) by blast
    have "row A' j1 \<bullet> x = b' $ j1" 
      using j1j2 
      by (metis \<open>x \<in> carrier_vec n \<and> A' *\<^sub>v x = b'\<close> index_mult_mat_vec)
    have "row A' j2 \<bullet> x = b' $ j2" 
      using j1j2 
      by (metis \<open>x \<in> carrier_vec n \<and> A' *\<^sub>v x = b'\<close> index_mult_mat_vec)

    then have "row A' j1 = row A' j2" using j1j2 
      by blast
    then show False 
      using \<open>b' $ j1 \<noteq> b' $ j2\<close> \<open>row A' j1 \<bullet> x = b' $ j1\<close> \<open>row A' j2 \<bullet> x = b' $ j2\<close> by presburger
  qed

  obtain C d where "(C, d) = sub_system A b (I - {i1})"
    by (metis surj_pair)
  have "{x.  A' *\<^sub>v x = b'} = {x.  C *\<^sub>v x = d \<and> row A i1 \<bullet> x = b $ i1 }"
    using remove_index_sub_system_eq[of A b i1 I A' b' C d] 
    by (metis A \<open>(C, d) = sub_system A b (I - {i1})\<close> i1 assms(8) b carrier_matD(1) carrier_vecD)
  have "\<forall>x.  C *\<^sub>v x = d \<longrightarrow> row A i1 \<bullet> x = b $ i1"
  proof(safe)
    fix x
    assume "d = C *\<^sub>v x" 
    have "i2 \<in> I - {i1}" 
      using \<open>i1 \<noteq> i2\<close> i2 by blast
    then obtain j where j: "j < dim_row C \<and> row A i2 = row C j \<and> b $ i2 = d $ j" 
      using exist_index_in_A'[of A b i2 "I - {i1}"] 
      by (metis A \<open>(C, d) = sub_system A b (I - {i1})\<close> i2 b carrier_matD(1) carrier_vecD dims_subsyst_same' fst_conv snd_conv)
    then have "row A i1 = row C j \<and> b $ i1 = d $ j" 
      by (metis \<open>b $ i1 = b $ i2\<close> i1 i2 j1j2)
    then have "row C j \<bullet> x = d $ j" using `d = C *\<^sub>v x`  j 
      by (metis index_mult_mat_vec)
    then show "row A i1 \<bullet> x = b $ i1" 
      by (metis \<open>b $ i1 = b $ i2\<close> i1 i2 j j1j2)
  qed
  then have "{x.  A' *\<^sub>v x = b'} = {x. C *\<^sub>v x = d}"
    using \<open>{x. A' *\<^sub>v x = b'} = {x. C *\<^sub>v x = d \<and> row A i1 \<bullet> x = b $ i1}\<close> by blast
  then have " F = {x. x \<in> carrier_vec n \<and> C *\<^sub>v x = d}" using assms(7)  
    by blast
  have "dim_vec d + 1 = dim_vec b'"
    using remove_index_sub_system_dims[of i1 I b A' b' A C d] 
    by (metis A \<open>(C, d) = sub_system A b (I - {i1})\<close> assms(8) b carrier_matD(1) carrier_vecD i1)
  then have "dim_vec d < Min {dim_vec d | C d I'.  F = {x. x \<in> carrier_vec n \<and> C *\<^sub>v x = d} \<and> 
          (C, d) = sub_system A b I'}" using assms(6) 
    by linarith
  have 1:"dim_vec d \<in>  {dim_vec d | C d I'.  F = {x. x \<in> carrier_vec n \<and> C *\<^sub>v x = d} \<and> 
          (C, d) = sub_system A b I'}" 
    using \<open>(C, d) = sub_system A b (I - {i1})\<close> \<open>{x. A' *\<^sub>v x = b'} = {x. C *\<^sub>v x = d}\<close> assms(7) by auto
  then have 2:"{dim_vec d | C d I'.  F = {x. x \<in> carrier_vec n \<and> C *\<^sub>v x = d} \<and> 
          (C, d) = sub_system A b I'} \<noteq> {}" 
    by blast
  then have 3:"finite {dim_vec d | C d I'.  F = {x. x \<in> carrier_vec n \<and> C *\<^sub>v x = d} \<and> 
          (C, d) = sub_system A b I'}"
    using subset_set_of_sub_dims_finite[of "{dim_vec d | C d I'.  F = {x. x \<in> carrier_vec n \<and> C *\<^sub>v x = d} \<and> 
          (C, d) = sub_system A b I'}" A b] 
    by fast
  then have "dim_vec d \<ge> Min {dim_vec d | C d I'.  F = {x. x \<in> carrier_vec n \<and> C *\<^sub>v x = d} \<and> 
          (C, d) = sub_system A b I'}" 
    using Min_eq_iff 1 2 3 
    by (meson Min_le)

  then show False using assms(6) `dim_vec d + 1 = dim_vec b'` 
    by linarith
qed

thm "Move_To_Matrix.transpose_vec_mult_scalar" 
thm "lindep_span" 

lemma gggd:
  assumes "u \<in> set L"
  obtains i where "u = L ! i" 
  by (metis assms in_set_conv_nth)


lemma vntero:
  fixes A :: "'a  mat"
  fixes b:: "'a vec" 
  assumes A: "A \<in> carrier_mat nr n"
  assumes b: "b \<in> carrier_vec nr"
  defines "P \<equiv> polyhedron A b"
  assumes "P \<noteq> {}"
  assumes "min_face P F"
  assumes "dim_vec b' = Min {dim_vec d | C d I'.  F = {x. x \<in> carrier_vec n \<and> C *\<^sub>v x = d} \<and> 
          (C, d) = sub_system A b I'}"
  assumes " F = {x. x \<in> carrier_vec n \<and> A' *\<^sub>v x = b'}"  
  assumes "(A', b') = sub_system A b I"
  shows "lin_indpt (set (rows A'))"
proof

  assume "lin_dep (set (rows A'))"
  have "distinct (rows A')" using  vnvnvnoo assms 
    by blast  
  have "set (rows A') \<subseteq> carrier_vec n"
    by (metis A assms(8) b carrier_matD(1) carrier_matD(2) carrier_mat_subsyst carrier_vecD prod.sel(1) set_rows_carrier subsetI)
  have "finite (set (rows A'))" 
    by simp
  have 1:"(\<exists>u\<in>(set (rows A')). u \<in> span ((set (rows A')) - {u}))" 

    using \<open>lin_dep (set (rows A'))\<close> \<open>set (rows A') \<subseteq> carrier_vec n\<close> lindep_span by blast
  then obtain u where u:"u\<in>(set (rows A'))\<and> u \<in> span ((set (rows A')) - {u})" by auto
  then obtain j where j':"j < length (rows  A') \<and> rows A' ! j = u" using in_set_conv_nth 
    by metis
  then have j:"j < dim_row A' \<and> row A' j = u" using nth_rows length_rows 
    by metis
  obtain i where i:"i < dim_row A \<and> i \<in> I \<and> row A i = row A' j \<and> i = (pick I j) \<and> b' $ j = b $ i" 
    using exist_index_in_A[of A b j I] 
    by (metis A assms(8) b carrier_matD(1) carrier_vecD dims_subsyst_same' fst_conv j snd_conv)

  obtain C d where C_d: "(C, d) = sub_system A b (I - {i})"
    by (metis surj_pair)
  have 4: "{x.  A' *\<^sub>v x = b'} = {x.  C *\<^sub>v x = d \<and> row A i \<bullet> x = b $ i }"
    using remove_index_sub_system_eq[of A b i I A' b' C d] 
    by (metis A \<open>(C, d) = sub_system A b (I - {i})\<close> i assms(8) b carrier_matD(1) carrier_vecD)
  have "\<forall>x \<in> carrier_vec n.  C *\<^sub>v x = d \<longrightarrow> row A i \<bullet> x = b $ i"
  proof(cases "u \<in> set (rows C)")
    case True
    then obtain j' where  "j' < length (rows C) \<and> (rows C) ! j' = u"  
      by (meson in_set_conv_nth)

    then have  j': "j' < dim_row C \<and> row C  j' = u"  
      using length_rows nth_rows by metis  
    obtain i' where i':"i' < dim_row A \<and> i' \<in> (I - {i}) \<and> row A i' = row C j' \<and> d $ j' = b $ i'" 
      using exist_index_in_A[of A b j' "I - {i}"] 
        A C_d  b carrier_matD(1) carrier_vecD dims_subsyst_same' fst_conv j' snd_conv
      by metis
    show ?thesis
    proof(safe)
      fix x
      assume " d = C *\<^sub>v x" 
      assume "x \<in> carrier_vec n" 
      have "row C j' \<bullet> x = d $ j'" 
        by (metis \<open>d = C *\<^sub>v x\<close> index_mult_mat_vec j')
      then have "row A i' \<bullet> x = b $ i'" 
        using i' by presburger
      have "b $ i' = b $ i" 
        by (smt (verit, best) "4" assms(5) assms(7) empty_Collect_eq face_non_empty i i' index_mult_mat_vec j j' min_face_elim(1))

      then show "row A i \<bullet> x = b $ i" 
        by (metis \<open>row A i' \<bullet> x = b $ i'\<close> i i' j j')
    qed
  next
    case False

    have "set (rows C) \<subseteq> carrier_vec n" 
      by (metis A C_d b carrier_matD(1) carrier_matD(2) carrier_mat_subsyst carrier_vecD prod.sel(1) set_rows_carrier subsetI)
    have "finite (set (rows A') - {u})" 
      by blast


    obtain  U a where U_a:"u = lincomb a U \<and> finite U \<and> U \<subseteq> set (rows A') - {u}" 
      unfolding span_def using 1   
      using in_spanE u by presburger
    then obtain c' where "u = lincomb c' (set (rows A') - {u})" using `finite (set (rows A') - {u})`
      by (metis \<open>set (rows A') \<subseteq> carrier_vec n\<close> finite_in_span insert_Diff_single insert_subset subset_code(1) u)

    then have "set (rows C) = set (rows A') - {u}" 
      using remove_index_remove_row[of A b i I A' b' C d] 
      by (metis A C_d False assms(8) b carrier_matD(1) carrier_vecD i j)
    then obtain c where "u = lincomb_list c (rows C)" 
      using  `set (rows C) \<subseteq> carrier_vec n`
      by (metis List.finite_set finite_in_span gram_schmidt.lincomb_then_lincomb_list u)
    then have 2:"u = sumlist (map (\<lambda>i. c i \<cdot>\<^sub>v  (rows C) ! i) [0..<length (rows C)])"
      using lincomb_list_def by presburger
    have 3:"(\<And>v. v \<in> set ((map (\<lambda>i. c i \<cdot>\<^sub>v  (rows C) ! i) [0..<length (rows C)])) \<Longrightarrow> v \<in> carrier_vec n)"
      by (smt (verit, best) \<open>set (rows C) \<subseteq> carrier_vec n\<close> in_set_conv_nth length_map map_nth nth_map smult_closed subsetD)

    have "\<forall>x \<in> carrier_vec n.  C *\<^sub>v x = d \<longrightarrow> row A' j \<bullet> x = sum_list  (map (\<lambda>i. (c i *  d $ i)) [0..<length (rows C)])" 
    proof(rule)+
      fix x
      assume "C *\<^sub>v x = d" 
      assume "x \<in> carrier_vec n" 
      then have "u \<bullet> x = sumlist (map (\<lambda>i. c i \<cdot>\<^sub>v  (rows C) ! i) [0..<length (rows C)]) \<bullet> x"
        using 2 by auto

      then have "u \<bullet> x = sum_list (map ((\<bullet>) x) (map (\<lambda>i. c i \<cdot>\<^sub>v  (rows C) ! i) [0..<length (rows C)]))"
        using scalar_prod_right_sum_distrib 3 `x \<in> carrier_vec n` 
        by (metis (no_types, lifting) "2" \<open>set (rows A') \<subseteq> carrier_vec n\<close> comm_scalar_prod subset_code(1) u)
      then have "u \<bullet> x = sum_list  (map (\<lambda>i. (c i \<cdot>\<^sub>v  (rows C) ! i) \<bullet> x) [0..<length (rows C)])"
        by (smt (verit, best) "3" \<open>x \<in> carrier_vec n\<close> comm_scalar_prod length_map map_eq_conv' nth_map nth_mem)
      then have "u \<bullet> x = sum_list  (map (\<lambda>i. (c i *  (((rows C) ! i) \<bullet> x))) [0..<length (rows C)])"
        by (smt (verit, ccfv_SIG) \<open>set (rows C) \<subseteq> carrier_vec n\<close> \<open>x \<in> carrier_vec n\<close> length_map map_eq_conv' map_nth nth_map nth_mem smult_scalar_prod_distrib subsetD)
      then have "u \<bullet> x = sum_list  (map (\<lambda>i. (c i *  d $ i)) [0..<length (rows C)])"
        by (smt (verit, ccfv_SIG) \<open>C *\<^sub>v x = d\<close> add.left_neutral index_mult_mat_vec length_map length_rows map_eq_conv' map_nth nth_rows nth_upt)
      then show " row A' j \<bullet> x = (\<Sum>i\<leftarrow>[0..<length (rows C)]. c i * d $ i)" 
        using j by blast
    qed

    have "b' $ j = sum_list (map (\<lambda>i. (c i *  d $ i)) [0..<length (rows C)])"
    proof(rule ccontr)
      assume "b' $ j \<noteq> (\<Sum>i\<leftarrow>[0..<length (rows C)]. c i * d $ i)" 
      then have "\<forall>x \<in> carrier_vec n.  C *\<^sub>v x = d \<longrightarrow> row A' j \<bullet> x \<noteq> b' $ j" 
        by (simp add: \<open>\<forall>x\<in>carrier_vec n. C *\<^sub>v x = d \<longrightarrow> row A' j \<bullet> x = (\<Sum>i\<leftarrow>[0..<length (rows C)]. c i * d $ i)\<close>)
      then have "{x. x \<in> carrier_vec n \<and>  C *\<^sub>v x = d \<and> row A' j \<bullet> x = b' $ j } = {}"  
        by blast
      then have "{x. x \<in> carrier_vec n \<and>  C *\<^sub>v x = d \<and> row A i \<bullet> x = b $ i } = {}" 
        by (metis  i)
      then have "{x. x \<in> carrier_vec n \<and> A' *\<^sub>v x = b'} = {}" using 4 
        by blast
      then show False 
        by (metis assms(5) assms(7) face_non_empty min_face_elim(1))
    qed

    show "\<forall>x \<in> carrier_vec n.  C *\<^sub>v x = d \<longrightarrow> row A i \<bullet> x = b $ i" 
      by (metis \<open>\<forall>x\<in>carrier_vec n. C *\<^sub>v x = d \<longrightarrow> row A' j \<bullet> x = (\<Sum>i\<leftarrow>[0..<length (rows C)]. c i * d $ i)\<close> \<open>b' $ j = (\<Sum>i\<leftarrow>[0..<length (rows C)]. c i * d $ i)\<close> i)
  qed
  then have "F = {x.  x \<in> carrier_vec n \<and> C *\<^sub>v x = d}" using 4  assms(7)
    by blast
  then have 5:"dim_vec d \<in> {dim_vec d | C d I'.  F = {x. x \<in> carrier_vec n \<and> C *\<^sub>v x = d} \<and> (C, d) = sub_system A b I'}"
    using `(C, d) = sub_system A b (I - {i})` 
    by blast 
  then have "{dim_vec d | C d I'.  F = {x. x \<in> carrier_vec n \<and> C *\<^sub>v x = d} \<and> (C, d) = sub_system A b I'} \<noteq> {}" by auto
  have "finite {dim_vec d | C d I'.  F = {x. x \<in> carrier_vec n \<and> C *\<^sub>v x = d} \<and> (C, d) = sub_system A b I'}"
    using subset_set_of_sub_dims_finite[of "{dim_vec d | C d I'.  F = {x. x \<in> carrier_vec n \<and> C *\<^sub>v x = d} \<and> (C, d) = sub_system A b I'}" A b]
    by blast
  then have "dim_vec b' \<le> dim_vec d"
    using  assms(6) 5
      Min_le[of  "{dim_vec d | C d I'.  F = {x. x \<in> carrier_vec n \<and> C *\<^sub>v x = d} \<and> (C, d) = sub_system A b I'}" "dim_vec d"]
    by presburger
  have "dim_vec b' = dim_vec d + 1"  
    using remove_index_sub_system_dims[of i I b A' b' A C d] 
    by (metis A \<open>(C, d) = sub_system A b (I - {i})\<close> assms(8) b carrier_matD(1) carrier_vecD i) 
  then show False using `dim_vec b' \<le> dim_vec d` 
    by linarith
qed


lemma bounded_min_faces_are_vertex:
  fixes A :: "'a  mat"
  fixes bound:: "'a" 
  assumes A: "A \<in> carrier_mat nr n"
  assumes b: "b \<in> carrier_vec nr"
  defines "P \<equiv> polyhedron A b"
  assumes "P \<noteq> {}"
  assumes bounded: "\<forall> x \<in> P. \<forall> i < n.  x $ i \<le> bound" 
  assumes "min_face P F"
  shows "card F = 1"
proof(cases "n = 0")
  case True
  have "{x |x. x \<in> carrier_vec 0} = {0\<^sub>v 0}" 
    by (metis (mono_tags, lifting) Collect_cong carrier_vecD singleton_conv vec_of_dim_0 zero_carrier_vec) 
  then have "P = {0\<^sub>v 0}" using assms(4) unfolding P_def polyhedron_def 
    using True by auto
  have "F = {0\<^sub>v 0}" 
    by (metis \<open>P = {0\<^sub>v 0}\<close> assms(6) face_non_empty face_subset_polyhedron min_face_elim(1) subset_singleton_iff)
  then show ?thesis 
    using card_eq_1_iff by blast
next
  case False
  have "\<forall> x \<in> P. \<forall> i < n. unit_vec n i \<bullet> x \<le> bound"
    using assms(5) scalar_prod_left_unit unfolding P_def polyhedron_def  
    by auto
  have "n > 0" using False by auto
  have "F \<noteq> {}" 
    using A P_def assms(6) b char_min_face by blast
  obtain \<alpha> \<beta> where "support_hyp P \<alpha> \<beta> \<and> F = P \<inter> {x |x. \<alpha> \<bullet> x = \<beta>}"
    using assms(6)
    by (metis faceE min_face_elim(1))
  obtain C d where C_d: "F = polyhedron C d"  "dim_row C = dim_vec d" "dim_col C = n" 
    using face_is_polyhedron 
    by (metis A P_def assms(6) b min_face_elim(1))
  have "\<exists>x\<in>carrier_vec n. C *\<^sub>v x \<le> d" 
    by (metis (mono_tags, lifting) A Collect_empty_eq P_def \<open>F = polyhedron C d\<close> assms(6) b char_min_face gram_schmidt.polyhedron_def)

  have "\<forall> i < n. \<exists> \<beta>\<^sub>i. \<forall>x \<in> F. x $ i = \<beta>\<^sub>i" 
  proof(rule)
    fix i
    show "i < n \<longrightarrow> (\<exists>\<beta>\<^sub>i. \<forall>x\<in>F. x $ i = \<beta>\<^sub>i)"
    proof
      assume "i < n" 
      have "\<forall> x \<in> F. unit_vec n i  \<bullet> x \<le> bound" 
        by (simp add: \<open>\<forall>x\<in>P. \<forall>i<n. unit_vec n i \<bullet> x \<le> bound\<close> \<open>i < n\<close> \<open>support_hyp P \<alpha> \<beta> \<and> F = P \<inter> {x |x. \<alpha> \<bullet> x = \<beta>}\<close>)

      then have  "\<forall> x \<in> carrier_vec n. C *\<^sub>v x \<le> d \<longrightarrow> unit_vec n i  \<bullet> x \<le> bound"
        by (simp add: \<open>F = polyhedron C d\<close> gram_schmidt.polyhedron_def)
      then have "has_Maximum {unit_vec n i  \<bullet> x | x. x \<in> carrier_vec n \<and> C *\<^sub>v x \<le> d}"
        using strong_duality_theorem_primal_sat_bounded_min_max(2)[of C _ n d "unit_vec n i"]
          C_d `\<exists>x\<in>carrier_vec n. C *\<^sub>v x \<le> d` 
        using unit_vec_carrier 
        using carrier_dim_vec by blast
      then obtain \<beta>\<^sub>i where "\<beta>\<^sub>i \<in> {unit_vec n i  \<bullet> x | x. x \<in> carrier_vec n \<and> C *\<^sub>v x \<le> d} 
        \<and> \<beta>\<^sub>i = Maximum {unit_vec n i  \<bullet> x | x. x \<in> carrier_vec n \<and> C *\<^sub>v x \<le> d}" 
        using has_MaximumD(1) by blast
      then have "support_hyp F (unit_vec n i) \<beta>\<^sub>i " 
        apply(intro support_hypI)
        unfolding C_d polyhedron_def
        using \<open>has_Maximum {unit_vec n i \<bullet> x |x. x \<in> carrier_vec n \<and> C *\<^sub>v x \<le> d}\<close> by auto+
      then have "face F (F\<inter>{x |x. (unit_vec n i) \<bullet> x = \<beta>\<^sub>i})" 
        using `F \<noteq> {}` by blast
      have "face P (F\<inter>{x |x. (unit_vec n i) \<bullet> x = \<beta>\<^sub>i})" 
        using face_trans[of A nr b F "(F\<inter>{x |x. (unit_vec n i) \<bullet> x = \<beta>\<^sub>i})"] 
        using A P_def \<open>face F (F \<inter> {x |x. unit_vec n i \<bullet> x = \<beta>\<^sub>i})\<close> assms(6) b min_face_elim(1) by presburger

      have "F = F\<inter>{x |x. (unit_vec n i) \<bullet> x = \<beta>\<^sub>i}"
      proof(rule ccontr)
        assume " F \<noteq> F \<inter> {x |x. unit_vec n i \<bullet> x = \<beta>\<^sub>i}"
        then have "F \<inter> {x |x. unit_vec n i \<bullet> x = \<beta>\<^sub>i} \<subset> F" 
          by blast
        then show False using `face P (F\<inter>{x |x. (unit_vec n i) \<bullet> x = \<beta>\<^sub>i})` 
          by (meson assms(6) min_face_elim(2))
      qed
      then have "\<forall> x \<in> F. (unit_vec n i) \<bullet> x = \<beta>\<^sub>i" by auto
      then have "\<forall> x \<in> F. x $ i = \<beta>\<^sub>i" 
        by (metis (no_types, lifting) IntE P_def \<open>\<And>thesis. (\<And>\<alpha> \<beta>. support_hyp P \<alpha> \<beta> \<and> F = P \<inter> {x |x. \<alpha> \<bullet> x = \<beta>} \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> \<open>i < n\<close> mem_Collect_eq polyhedron_def scalar_prod_left_unit)

      then show "(\<exists>\<beta>\<^sub>i. \<forall>x\<in>F. x $ i = \<beta>\<^sub>i)" by auto
    qed
  qed
  have "\<exists>! x. x \<in> F"
  proof(rule ccontr)
    assume "\<nexists>!x. x \<in> F"
    then obtain x y where "x \<in> F \<and> y \<in> F \<and> x \<noteq> y" 
      using \<open>F \<noteq> {}\<close> by blast
    then obtain i where "i < n \<and> x $ i \<noteq> y $ i" 
      by (metis (no_types, lifting) A P_def assms(6) b carrier_dim_vec char_min_face eq_vecI mem_Collect_eq)
    have "\<exists>\<beta>\<^sub>i. \<forall>x\<in>F. x $ i = \<beta>\<^sub>i" 
      using \<open>\<forall>i<n. \<exists>\<beta>\<^sub>i. \<forall>x\<in>F. x $ i = \<beta>\<^sub>i\<close> \<open>i < n \<and> x $ i \<noteq> y $ i\<close> by presburger
    then show False 
      by (metis \<open>i < n \<and> x $ i \<noteq> y $ i\<close> \<open>x \<in> F \<and> y \<in> F \<and> x \<noteq> y\<close>)
  qed
  then show "card F = 1" 
    by (metis \<open>F \<noteq> {}\<close> is_singletonI' is_singleton_altdef)
qed

thm "lin_depE"

lemma (in vec_space) lin_depE1:
  assumes "A \<in> carrier_mat n n"
  assumes "lin_dep (set (cols A))"
  assumes "distinct (cols A)"
  obtains v where "v \<in> carrier_vec n" "v \<noteq> 0\<^sub>v n" "A *\<^sub>v v = 0\<^sub>v n"
  using lin_depE assms 
  by blast

lemma (in vec_space) lin_dep_cols_iff_rows:
  assumes "A \<in> carrier_mat n n"
  assumes "distinct (cols A)"
  assumes "distinct (rows A)"
  shows "lin_dep (set (rows A)) = lin_dep (set (cols A))"
  by (metis assms cols_transpose det_rank_iff det_transpose idom_vec.lin_dep_cols_imp_det_0 transpose_carrier_mat vec_space.lin_indpt_full_rank)


lemma cvbr:
  fixes A :: "'a  mat"
  assumes "A \<in> carrier_mat nr n"
  assumes "i < n"
  shows "A *\<^sub>v unit_vec n i = col A i" 
proof
  show "dim_vec (A *\<^sub>v unit_vec n i) = dim_vec (col A i)" 
    by (metis dim_col dim_mult_mat_vec)
  fix j
  assume "j < dim_vec (col A i)"
  have "(A *\<^sub>v unit_vec n i) $ j = row A j \<bullet> unit_vec n i" 
    by (metis \<open>j < dim_vec (col A i)\<close> dim_col index_mult_mat_vec)
  have " row A j \<bullet> unit_vec n i = row A j $ i" 
    using assms(2) scalar_prod_right_unit by blast
  have "row A j $ i = col A i $ j" 
    by (metis \<open>j < dim_vec (col A i)\<close> assms(1) assms(2) carrier_matD(2) dim_col index_col index_row(1))
  show "(A *\<^sub>v unit_vec n i) $ j = col A i $ j" 
    using \<open>(A *\<^sub>v unit_vec n i) $ j = row A j \<bullet> unit_vec n i\<close> \<open>row A j $ i = col A i $ j\<close> \<open>row A j \<bullet> unit_vec n i = row A j $ i\<close> by presburger
qed

lemma gfgd:
  fixes A :: "'a  mat"
  assumes "A \<in> carrier_mat nr1 n"
  assumes "B \<in> carrier_mat nr2 n"
  assumes "distinct (cols A)"
  shows "distinct (cols (A @\<^sub>r B))"
proof -
  have "dim_row (A @\<^sub>r B) = nr1 + nr2" 
    using assms(1) assms(2) carrier_matD(1) by blast
  have "dim_col (A @\<^sub>r B) = n" 
    using assms(1) assms(2) carrier_matD(2) by blast

  have "(submatrix (A @\<^sub>r B) {0..<nr1} UNIV) = A"
  proof
    have "{i. i<dim_row (A @\<^sub>r B) \<and> i\<in> {0..<nr1}} = {0..<nr1}" 
      using `dim_row (A @\<^sub>r B) = nr1 + nr2` 
      by fastforce 
    then have "(card {i. i<dim_row (A @\<^sub>r B) \<and> i\<in> {0..<nr1}}) =  nr1" 
      by auto  

    show "dim_row (submatrix (A @\<^sub>r B) {0..<nr1} UNIV) = dim_row A" 
      using dim_submatrix[of "(A @\<^sub>r B)" "{0..<nr1}"]  
        `(card {i. i<dim_row (A @\<^sub>r B) \<and> i\<in> {0..<nr1}}) = nr1` assms(1) 
      by (metis carrier_matD(1))

    show "dim_col (submatrix (A @\<^sub>r B) {0..<nr1} UNIV) = dim_col A"  
      using dim_submatrix(2)[of "(A @\<^sub>r B)" "{0..<nr1}" UNIV]  
      by (metis \<open>dim_col (A @\<^sub>r B) = n\<close>  assms(1) carrier_matD(2) dim_col_subsyst_mat sub_system_fst)

    fix i j
    assume "i < dim_row A"
    assume "j < dim_col A"
    show " submatrix (A @\<^sub>r B) {0..<nr1} UNIV $$ (i, j) = A $$ (i, j)"
    proof -
      have "i < nr1" using `i < dim_row A` 
        using assms(1) by blast
      then have "{a\<in>{0..<nr1}. a < i} = {0..<i}" 
        by auto
      then have "card {a\<in>{0..<nr1}. a < i} = i" 
        by simp
      have "submatrix (A @\<^sub>r B) {0..<nr1} UNIV $$ (card {a\<in>{0..<nr1}. a < i}, card {a\<in>UNIV. a < j}) =
       (A @\<^sub>r B) $$ (i, j)" 
        using submatrix_index_card[of i "A @\<^sub>r B" j "{0..<nr1}" UNIV] 
        by (metis UNIV_I \<open>dim_col (A @\<^sub>r B) = n\<close> \<open>dim_row (A @\<^sub>r B) = nr1 + nr2\<close> \<open>i < dim_row A\<close> \<open>j < dim_col A\<close> assms(1) atLeastLessThan_iff carrier_matD(1) carrier_matD(2) trans_less_add1 zero_le)

      then have "submatrix (A @\<^sub>r B) {0..<nr1} UNIV $$ (i, j) =  (A @\<^sub>r B) $$ (i, j)" 
        using \<open>card {a \<in> {0..<nr1}. a < i} = i\<close> by force
      have " (A @\<^sub>r B) $$ (i, j) =  A $$ (i, j)" 
        by (metis (mono_tags, lifting) \<open>dim_col (A @\<^sub>r B) = n\<close> \<open>dim_row (A @\<^sub>r B) = nr1 + nr2\<close> \<open>i < dim_row A\<close> \<open>j < dim_col A\<close> append_rows_index_same assms(1) assms(2) carrier_matD(1) carrier_matD(2) index_row(1) trans_less_add1)
      then show "submatrix (A @\<^sub>r B) {0..<nr1} UNIV $$ (i, j) = A $$ (i, j)" 
        using \<open>submatrix (A @\<^sub>r B) {0..<nr1} UNIV $$ (i, j) = (A @\<^sub>r B) $$ (i, j)\<close> by presburger
    qed
  qed
  then show ?thesis using distinct_cols_submatrix_UNIV 
    by (metis assms(3))
qed

lemma append_rows_eq: assumes A: "A \<in> carrier_mat nr1 nc" 
  and B: "B \<in> carrier_mat nr2 nc" 
  and a: "a \<in> carrier_vec nr1" 
  and v: "v \<in> carrier_vec nc"
shows "(A @\<^sub>r B) *\<^sub>v v = (a @\<^sub>v b) \<longleftrightarrow> A *\<^sub>v v = a \<and> B *\<^sub>v v = b" 
  unfolding mat_mult_append[OF A B v]
  by (rule append_vec_eq[OF _ a], insert A v, auto)

lemma vvnvnvwwcc:
  assumes "v \<in> carrier_vec n"
  assumes "u \<in> carrier_vec n"
  assumes "v = k \<cdot>\<^sub>v u"
  assumes "v \<noteq> u"
  assumes "u \<in> S"
  assumes "v \<in> S"
  shows "lin_dep S"
proof -
  have "0\<^sub>v n = v - k \<cdot>\<^sub>v u " 
    using assms(1) assms(3) by force
  let ?a = "(\<lambda> x. 0)(u:= -k, v:= 1)"
  have "lincomb ?a {u, v} = lincomb ?a {v} + ?a u \<cdot>\<^sub>v u" 
    using M.add.m_comm assms(1) assms(2) assms(4) lincomb_insert by force
  then have "lincomb ?a {u, v} = ?a v \<cdot>\<^sub>v v + ?a u \<cdot>\<^sub>v u + lincomb ?a {}" 
    using assms(1) assms(3) lincomb_insert by fastforce
  then have "lincomb ?a {u, v} = ?a v \<cdot>\<^sub>v v + ?a u \<cdot>\<^sub>v u + 0\<^sub>v n" 
    using lincomb_empty by presburger
  then have "lincomb ?a {u, v} = 1 \<cdot>\<^sub>v v + (-k)\<cdot>\<^sub>v u" 
    using assms(2) assms(3) assms(4) by force
  then have "0\<^sub>v n = lincomb ?a {u, v}" 
    using assms(2) assms(3) by force
  have "finite {u, v}" by auto
  have "{u, v} \<subseteq> S" using assms(5-6) by auto
  have "?a v \<noteq> 0" by auto
  then show ?thesis unfolding lin_dep_def  `0\<^sub>v n = lincomb ?a {u, v}`  
    using \<open>finite {u, v}\<close> \<open>{u, v} \<subseteq> S\<close> by blast
qed

lemma  dasdasd:
  fixes A :: "'a  mat"
  assumes "A \<in> carrier_mat nr n"
  assumes "i < nr"
  assumes "j < nr"
  assumes "k \<noteq> 1" 
  assumes "row A i = k \<cdot>\<^sub>v row A j"
  shows "lin_dep (set (rows A))"
proof(cases "row A i = 0\<^sub>v n")
  case True
  then have "0\<^sub>v n \<in> (set (rows A))" 
    by (metis assms(1) assms(2) carrier_matD(1) in_set_conv_nth length_rows nth_rows)
  then show ?thesis 
    by (metis assms(1) carrier_matD(2) rows_carrier vs_zero_lin_dep)
next
  case False
  then show ?thesis
  proof(cases "row A j = 0\<^sub>v n")
    case True
    then have "0\<^sub>v n \<in> (set (rows A))" 
      by (metis assms(1) assms(3) carrier_matD(1) in_set_conv_nth length_rows nth_rows)
    then show ?thesis 
      by (metis assms(1) carrier_matD(2) rows_carrier vs_zero_lin_dep)
  next
    case False

    have "row A i \<noteq> row A j"
    proof(rule ccontr)
      assume " \<not> row A i \<noteq> row A j"
      then have "row A i = row A j" by auto
      obtain l where "l < n \<and> row A i $ l \<noteq> 0" 
        by (metis False M.zero_closed \<open>row A i = row A j\<close> assms(1) assms(2) carrier_vecD eq_vecI index_zero_vec(1) row_carrier_vec)
      then have "row A i $ l = row A j $ l" 
        using \<open>\<not> row A i \<noteq> row A j\<close> by presburger
      have "row A i $ l = k * row A j $ l" 
        by (metis \<open>l < n \<and> row A i $ l \<noteq> 0\<close> \<open>row A i = row A j\<close> assms(1) assms(2) assms(5) carrier_vecD index_smult_vec(1) row_carrier_vec)
      then show False 
        by (metis \<open>l < n \<and> row A i $ l \<noteq> 0\<close> \<open>row A i $ l = row A j $ l\<close> assms(4) m_comm mult_cancel_left r_one)
    qed
    then show ?thesis using vvnvnvwwcc[of "row A i" "row A j" k " (set (rows A))"] 
      by (metis assms(1) assms(2) assms(3) assms(5) carrier_matD(1) in_set_conv_nth length_rows nth_rows row_carrier_vec)
  qed
qed


lemma  lin_depE1assd:
  fixes A :: "'a  mat"
  assumes "A \<in> carrier_mat nr n"
  assumes b: "b \<in> carrier_vec nr"
  assumes "\<exists>! x \<in> carrier_vec n. A *\<^sub>v x = b"
  assumes "lin_indpt (set (rows A))"
  assumes "distinct (rows A)"
  shows "nr = n" 
proof(cases "nr = 0")
  case True
    then have "nr = 0" by auto
    then have "\<forall>x \<in> carrier_vec n.  A *\<^sub>v x = b" 
      by (metis assms(1) b carrier_matD(1) carrier_vecD dim_mult_mat_vec vec_of_dim_0)
    have "\<exists>!(x:: 'a vec).  x \<in> carrier_vec n" 
      using \<open>\<forall>x\<in>carrier_vec n. A *\<^sub>v x = b\<close> assms(3) by auto
    
    have "n = 0 "
    proof(rule ccontr)
      assume "n \<noteq> 0" 
      have "(1\<^sub>v n:: 'a vec) \<in> carrier_vec n" by auto
      have "(0\<^sub>v n:: 'a vec) \<in> carrier_vec n" by auto
      have "(1\<^sub>v n:: 'a vec) \<noteq> (1\<^sub>v n:: 'a vec)" 
        by (metis M.zero_closed \<open>\<exists>!x. x \<in> carrier_vec n\<close> \<open>n \<noteq> 0\<close> gr_zeroI index_one_vec(1) index_zero_vec(1) one_carrier_vec zero_not_one)
        then show False using `(1\<^sub>v n:: 'a vec) \<in> carrier_vec n` `(0\<^sub>v n:: 'a vec) \<in> carrier_vec n` 
              `\<exists>!(x:: 'a vec).  x \<in> carrier_vec n`
          by blast
      qed
      then show ?thesis using True by auto
    next
      case False
      then have "nr > 0" by auto
  have "distinct (cols A)"
  proof(rule ccontr)
    assume "\<not> distinct (cols A)" 
    then obtain i j where "i < length (cols  A) \<and> j < length (cols  A) \<and> i \<noteq> j \<and> cols A ! i = cols A ! j" 
      using distinct_conv_nth by blast
    then have "i < n \<and> j < n \<and> i \<noteq> j \<and> col A  i = col A j" 
      by (metis assms(1) carrier_matD(2) cols_length cols_nth)
    obtain x where "x \<in> carrier_vec n \<and> A *\<^sub>v x = b" using assms(3) by auto

    let ?y = "x + (unit_vec n i) - (unit_vec n j)"
    have "?y \<in> carrier_vec n" 
      by (simp add: \<open>x \<in> carrier_vec n \<and> A *\<^sub>v x = b\<close>)
    have " A *\<^sub>v ?y= b"
    proof -
      have "A *\<^sub>v (x + unit_vec n i - unit_vec n j) = A *\<^sub>v x + A *\<^sub>v unit_vec n i - A *\<^sub>v unit_vec n j" 
        by (smt (verit) M.add.m_closed \<open>x \<in> carrier_vec n \<and> A *\<^sub>v x = b\<close> assms(1) mult_add_distrib_mat_vec mult_minus_distrib_mat_vec unit_vec_carrier)
      have "A *\<^sub>v unit_vec n i = col A i" using cvbr 
        using \<open>i < n \<and> j < n \<and> i \<noteq> j \<and> col A i = col A j\<close> assms(1) by blast
      have "A *\<^sub>v unit_vec n j = col A j" using cvbr 
        using \<open>i < n \<and> j < n \<and> i \<noteq> j \<and> col A i = col A j\<close> assms(1) by blast
      have "A *\<^sub>v unit_vec n i - A *\<^sub>v unit_vec n j = 0\<^sub>v nr" 
        by (metis \<open>A *\<^sub>v unit_vec n i = col A i\<close> \<open>A *\<^sub>v unit_vec n j = col A j\<close> \<open>i < n \<and> j < n \<and> i \<noteq> j \<and> col A i = col A j\<close> assms(1) col_carrier_vec minus_cancel_vec)
      show "A *\<^sub>v ?y= b" 
        by (metis \<open>A *\<^sub>v (x + unit_vec n i - unit_vec n j) = A *\<^sub>v x + A *\<^sub>v unit_vec n i - A *\<^sub>v unit_vec n j\<close> \<open>A *\<^sub>v unit_vec n i - A *\<^sub>v unit_vec n j = 0\<^sub>v nr\<close> \<open>A *\<^sub>v unit_vec n i = col A i\<close> \<open>A *\<^sub>v unit_vec n j = col A j\<close> \<open>i < n \<and> j < n \<and> i \<noteq> j \<and> col A i = col A j\<close> \<open>x \<in> carrier_vec n \<and> A *\<^sub>v x = b\<close> add_diff_eq_vec assms(1) b col_carrier_vec right_zero_vec)
    qed
    have "x \<noteq> ?y"
    proof(rule ccontr)
      assume "\<not> (x \<noteq> ?y)"
      then have "x = ?y" by auto
      then have "x $ i = ?y $ i" 
        by force
      have "?y $ i = x $ i + unit_vec n i $ i - unit_vec n j $ i" 
        by (simp add: \<open>i < n \<and> j < n \<and> i \<noteq> j \<and> col A i = col A j\<close>)
      then have "unit_vec n i $ i - unit_vec n j $ i = 0" 
        using \<open>i < n \<and> j < n \<and> i \<noteq> j \<and> col A i = col A j\<close> \<open>x = x + unit_vec n i - unit_vec n j\<close> by auto
      then show False 
        using \<open>i < n \<and> j < n \<and> i \<noteq> j \<and> col A i = col A j\<close> index_unit_vec(1) by fastforce
    qed
    then show False 
      using \<open>A *\<^sub>v (x + unit_vec n i - unit_vec n j) = b\<close> \<open>x + unit_vec n i - unit_vec n j \<in> carrier_vec n\<close> \<open>x \<in> carrier_vec n \<and> A *\<^sub>v x = b\<close> assms(3) by blast
  qed
  have "rank A\<^sup>T = nr" 
    by (simp add: assms(1) assms(4) assms(5) vec_space.lin_indpt_full_rank)
  have "set (rows A) \<subseteq> carrier_vec n" 
    using assms(1) set_rows_carrier by blast
  then have "(set (cols A\<^sup>T)) \<subseteq> carrier_vec n" 
    by simp 
  then have "dim_span (set (cols A\<^sup>T)) \<le> n" using dim_span_le_n 
    by blast
  have "rank A\<^sup>T = dim_span (set (cols A\<^sup>T))" 
    by (metis \<open>rank A\<^sup>T = nr\<close> \<open>set (cols A\<^sup>T) \<subseteq> carrier_vec n\<close> assms(1) assms(4) assms(5) carrier_matD(1) cols_length cols_transpose distinct_card index_transpose_mat(3) same_span_imp_card_eq_dim_span)
  then have "nr \<le> n" 
    using \<open>dim_span (set (cols A\<^sup>T)) \<le> n\<close> \<open>rank A\<^sup>T = nr\<close> by presburger


  show "nr = n"
  proof(cases "nr < n")
    case True
    then show ?thesis 
    proof -
      let ?fullb = "b @\<^sub>v (vec n (\<lambda> k. (of_int k + 2) * b $ 0 ))"

      let ?rows = "map (\<lambda> k. (of_int k + 2) \<cdot>\<^sub>v row A 0) [0..<n-nr]"
      let ?app_rows = "mat_of_rows n ?rows"
      let ?fullA = "A @\<^sub>r ?app_rows" 
      have sq_fullA: "?fullA \<in> carrier_mat n n" 
        by (metis (no_types, lifting) \<open>nr \<le> n\<close> assms(1) carrier_append_rows diff_zero le_add_diff_inverse length_map length_upt mat_carrier mat_of_rows_def)
      have "?app_rows \<in> carrier_mat (n-nr) n" 
        by (simp add: mat_of_rows_def)
      then have "dim_row ?app_rows = n - nr" 
        by blast
      have "distinct (rows ?fullA)"
      proof(rule ccontr)
        assume "\<not> distinct (rows ?fullA)" 
        then obtain i j where "i < n \<and> j < n \<and> i \<noteq> j \<and> rows ?fullA ! i = rows ?fullA ! j" 
          by (metis sq_fullA carrier_matD(1) distinct_conv_nth length_rows)
        then have i_j:"i < n \<and> j < n \<and> i \<noteq> j \<and> row ?fullA  i = row ?fullA j"  
          by (metis sq_fullA carrier_matD(1) nth_rows)
        show False
        proof(cases "i < nr")
          case True
          have "row ?fullA  i = row A i" using True 
            by (metis append_rows_index_same assms(1) carrier_matD(1) mat_carrier mat_of_rows_def)
          show ?thesis
          proof(cases "j < nr")
            case True
            have "row ?fullA  j = row A j"
              using True 
              by (metis append_rows_index_same assms(1) carrier_matD(1) mat_carrier mat_of_rows_def)
            then have "rows A ! i = rows A ! j" using `row ?fullA  i = row A i` i_j 
                nth_rows `i < nr` `j < nr` `A \<in> carrier_mat nr n`  carrier_matD(1) 
              by metis 
            have "i < length (rows A)" using length_rows assms(1) carrier_matD(1) `i < nr` 
              by metis  
            have "j < length (rows A)" using length_rows assms(1) carrier_matD(1) `j < nr` 
              by metis 
            then show ?thesis using `i < length (rows A)`  assms(5) distinct_conv_nth  
              using \<open>rows A ! i = rows A ! j\<close> i_j by blast
          next
            case False
            then have "j - nr < dim_row ?app_rows" 
              by (simp add: diff_less_mono i_j) 
            have "nr \<le> j" using False by auto
            have "j < nr + (n - nr)" using False i_j 
              by linarith
            then have "row ?fullA  j = row ?app_rows (j-nr)" using  
                append_rows_nth(2)[of A nr n ?app_rows "n-nr" j] `nr \<le> j` `?app_rows \<in> carrier_mat (n-nr) n` 
                assms(1) 
              by blast 
            have "row ?app_rows (j-nr) = rows ?app_rows ! (j-nr)" 
              by (metis \<open>j - nr < dim_row (mat_of_rows n (map (\<lambda>k. (of_int k + 2) \<cdot>\<^sub>v row A 0) (map int [0..<n - nr])))\<close> nth_rows)
            have "rows ?app_rows ! (j-nr) = (map (\<lambda>k. (of_int k + 2) \<cdot>\<^sub>v row A 0) (map int [0..<n - nr])) ! (j-nr)"
              by (metis (no_types, lifting) \<open>j - nr < dim_row (mat_of_rows n (map (\<lambda>k. (of_int k + 2) \<cdot>\<^sub>v row A 0) (map int [0..<n - nr])))\<close> assms(1) carrier_matD(2) length_map mat_of_rows_carrier(2) mat_of_rows_row nth_map nth_rows row_carrier smult_closed)
            have "(map (\<lambda>k. (of_int k + 2) \<cdot>\<^sub>v row A 0) (map int [0..<n - nr])) ! (j-nr) = 
                of_int ((j - nr) + 2) \<cdot>\<^sub>v row A 0" 
              using \<open>j - nr < dim_row (mat_of_rows n (map (\<lambda>k. (of_int k + 2) \<cdot>\<^sub>v row A 0) (map int [0..<n - nr])))\<close> by auto
            then have "row ?fullA  j = of_int ((j - nr) + 2) \<cdot>\<^sub>v row A 0" 
              using \<open>row (A @\<^sub>r mat_of_rows n (map (\<lambda>k. (of_int k + 2) \<cdot>\<^sub>v row A 0) (map int [0..<n - nr]))) j = row (mat_of_rows n (map (\<lambda>k. (of_int k + 2) \<cdot>\<^sub>v row A 0) (map int [0..<n - nr]))) (j - nr)\<close> \<open>row (mat_of_rows n (map (\<lambda>k. (of_int k + 2) \<cdot>\<^sub>v row A 0) (map int [0..<n - nr]))) (j - nr) = rows (mat_of_rows n (map (\<lambda>k. (of_int k + 2) \<cdot>\<^sub>v row A 0) (map int [0..<n - nr]))) ! (j - nr)\<close> \<open>rows (mat_of_rows n (map (\<lambda>k. (of_int k + 2) \<cdot>\<^sub>v row A 0) (map int [0..<n - nr]))) ! (j - nr) = map (\<lambda>k. (of_int k + 2) \<cdot>\<^sub>v row A 0) (map int [0..<n - nr]) ! (j - nr)\<close> by presburger
            then have "row A i = of_int ((j - nr) + 2) \<cdot>\<^sub>v row A 0" 
              using \<open>row (A @\<^sub>r mat_of_rows n (map (\<lambda>k. (of_int k + 2) \<cdot>\<^sub>v row A 0) (map int [0..<n - nr]))) i = row A i\<close> i_j by presburger
            then show ?thesis using dasdasd[of A nr i 0 "of_int ((j - nr) + 2)"] 
              using True assms(1) assms(4) by fastforce
          qed
        next
          case False
          then have "i \<ge> nr" by auto 
          then have "i - nr < dim_row ?app_rows" 
            by (simp add: diff_less_mono i_j) 
          have "i < nr + (n - nr)" using False i_j 
            by linarith
          then have "row ?fullA i = row ?app_rows (i-nr)" using  
              append_rows_nth(2)[of A nr n ?app_rows "n-nr" i] `nr \<le> i` `?app_rows \<in> carrier_mat (n-nr) n` 
            by (metis  assms(1))
          have "row ?app_rows (i-nr) = rows ?app_rows ! (i-nr)" 
            by (metis \<open>i - nr < dim_row (mat_of_rows n (map (\<lambda>k. (of_int k + 2) \<cdot>\<^sub>v row A 0) (map int [0..<n - nr])))\<close> nth_rows)
          have "rows ?app_rows ! (i-nr) = (map (\<lambda>k. (of_int k + 2) \<cdot>\<^sub>v row A 0) (map int [0..<n - nr])) ! (i-nr)"
            by (metis (no_types, lifting) \<open>i - nr < dim_row (mat_of_rows n (map (\<lambda>k. (of_int k + 2) \<cdot>\<^sub>v row A 0) (map int [0..<n - nr])))\<close> assms(1) carrier_matD(2) length_map mat_of_rows_carrier(2) mat_of_rows_row nth_map nth_rows row_carrier smult_closed)
          have "(map (\<lambda>k. (of_int k + 2) \<cdot>\<^sub>v row A 0) (map int [0..<n - nr])) ! (i-nr) = 
                of_int ((i - nr) + 2) \<cdot>\<^sub>v row A 0" 
            using \<open>i - nr < dim_row (mat_of_rows n (map (\<lambda>k. (of_int k + 2) \<cdot>\<^sub>v row A 0) (map int [0..<n - nr])))\<close> by auto
          then have "row ?fullA i = of_int ((i - nr) + 2) \<cdot>\<^sub>v row A 0" 
            using \<open>row (A @\<^sub>r mat_of_rows n (map (\<lambda>k. (of_int k + 2) \<cdot>\<^sub>v row A 0) (map int [0..<n - nr]))) i = row (mat_of_rows n (map (\<lambda>k. (of_int k + 2) \<cdot>\<^sub>v row A 0) (map int [0..<n - nr]))) (i - nr)\<close> \<open>row (mat_of_rows n (map (\<lambda>k. (of_int k + 2) \<cdot>\<^sub>v row A 0) (map int [0..<n - nr]))) (i - nr) = rows (mat_of_rows n (map (\<lambda>k. (of_int k + 2) \<cdot>\<^sub>v row A 0) (map int [0..<n - nr]))) ! (i - nr)\<close> \<open>rows (mat_of_rows n (map (\<lambda>k. (of_int k + 2) \<cdot>\<^sub>v row A 0) (map int [0..<n - nr]))) ! (i - nr) = map (\<lambda>k. (of_int k + 2) \<cdot>\<^sub>v row A 0) (map int [0..<n - nr]) ! (i - nr)\<close> by presburger

          show ?thesis 
          proof(cases "j < nr")
            case True
            have "row ?fullA  j = row A j"
              using True 
              by (metis append_rows_index_same assms(1) carrier_matD(1) mat_carrier mat_of_rows_def)
            have "row A j = of_int ((i - nr) + 2) \<cdot>\<^sub>v row A 0" 
              using `row ?fullA i = of_int ((i - nr) + 2) \<cdot>\<^sub>v row A 0` 
                \<open>row (A @\<^sub>r mat_of_rows n (map (\<lambda>k. (of_int k + 2) \<cdot>\<^sub>v row A 0) (map int [0..<n - nr]))) j = row A j\<close> i_j by presburger
            then show ?thesis using dasdasd[of A nr j 0 "of_int ((i - nr) + 2)"] `nr \<noteq> 0` 
              using True assms(1) assms(4) by fastforce
          next
            case False
            then have "j - nr < dim_row ?app_rows" 
              by (simp add: diff_less_mono i_j) 
            have "nr \<le> j" using False by auto
            have "j < nr + (n - nr)" using False i_j 
              by linarith
            then have "row ?fullA  j = row ?app_rows (j-nr)" using  
                append_rows_nth(2)[of A nr n ?app_rows "n-nr" j] `nr \<le> j` `?app_rows \<in> carrier_mat (n-nr) n` 
                assms(1) 
              by blast 
            have "row ?app_rows (j-nr) = rows ?app_rows ! (j-nr)" 
              by (metis \<open>j - nr < dim_row (mat_of_rows n (map (\<lambda>k. (of_int k + 2) \<cdot>\<^sub>v row A 0) (map int [0..<n - nr])))\<close> nth_rows)
            have "rows ?app_rows ! (j-nr) = (map (\<lambda>k. (of_int k + 2) \<cdot>\<^sub>v row A 0) (map int [0..<n - nr])) ! (j-nr)"
              by (metis (no_types, lifting) \<open>j - nr < dim_row (mat_of_rows n (map (\<lambda>k. (of_int k + 2) \<cdot>\<^sub>v row A 0) (map int [0..<n - nr])))\<close> assms(1) carrier_matD(2) length_map mat_of_rows_carrier(2) mat_of_rows_row nth_map nth_rows row_carrier smult_closed)
            have "(map (\<lambda>k. (of_int k + 2) \<cdot>\<^sub>v row A 0) (map int [0..<n - nr])) ! (j-nr) = 
                of_int ((j - nr) + 2) \<cdot>\<^sub>v row A 0" 
              using \<open>j - nr < dim_row (mat_of_rows n (map (\<lambda>k. (of_int k + 2) \<cdot>\<^sub>v row A 0) (map int [0..<n - nr])))\<close> by auto
            then have "row ?fullA  j = of_int ((j - nr) + 2) \<cdot>\<^sub>v row A 0" 
              using \<open>row (A @\<^sub>r mat_of_rows n (map (\<lambda>k. (of_int k + 2) \<cdot>\<^sub>v row A 0) (map int [0..<n - nr]))) j = row (mat_of_rows n (map (\<lambda>k. (of_int k + 2) \<cdot>\<^sub>v row A 0) (map int [0..<n - nr]))) (j - nr)\<close> \<open>row (mat_of_rows n (map (\<lambda>k. (of_int k + 2) \<cdot>\<^sub>v row A 0) (map int [0..<n - nr]))) (j - nr) = rows (mat_of_rows n (map (\<lambda>k. (of_int k + 2) \<cdot>\<^sub>v row A 0) (map int [0..<n - nr]))) ! (j - nr)\<close> \<open>rows (mat_of_rows n (map (\<lambda>k. (of_int k + 2) \<cdot>\<^sub>v row A 0) (map int [0..<n - nr]))) ! (j - nr) = map (\<lambda>k. (of_int k + 2) \<cdot>\<^sub>v row A 0) (map int [0..<n - nr]) ! (j - nr)\<close> by presburger
            then have "of_int ((i - nr) + 2) \<cdot>\<^sub>v row A 0 = of_int ((j - nr) + 2) \<cdot>\<^sub>v row A 0"
              using \<open>row (A @\<^sub>r mat_of_rows n (map (\<lambda>k. (of_int k + 2) \<cdot>\<^sub>v row A 0) (map int [0..<n - nr]))) i = of_int (int (i - nr + 2)) \<cdot>\<^sub>v row A 0\<close> i_j by presburger
            then have "of_int ((i - nr) + 2) \<cdot>\<^sub>v row A 0 - of_int ((j - nr) + 2) \<cdot>\<^sub>v row A 0 = 0\<^sub>v n"
              using  `nr > 0` 
              by (metis assms(1)  minus_cancel_vec row_carrier_vec smult_closed)
            then have "(of_int ((i - nr) + 2) - of_int ((j - nr) + 2)) \<cdot>\<^sub>v row A 0 = 0\<^sub>v n" 
              by (metis diff_smult_distrib_vec)
            show ?thesis
            proof(cases "row A 0 = 0\<^sub>v n")
              case True
              then have "0\<^sub>v n \<in> (set (rows A))"  
                by (metis assms(1) `nr > 0` carrier_matD(1) in_set_conv_nth length_rows nth_rows)
              then show ?thesis 
                using \<open>set (rows A) \<subseteq> carrier_vec n\<close> assms(4) vs_zero_lin_dep by blast
            next
              case False
              then obtain l where "l < n \<and> row A 0 $ l \<noteq> 0" 
                by (metis M.zero_closed assms(1) `nr > 0` carrier_vecD eq_vecI index_zero_vec(1) row_carrier_vec)
              then have "((of_int ((i - nr) + 2) - of_int ((j - nr) + 2)) \<cdot>\<^sub>v row A 0) $ l = 
                      (of_int ((i - nr) + 2) - of_int ((j - nr) + 2)) * row A 0 $ l" 
                by (metis assms(1) `nr > 0` carrier_vecD index_smult_vec(1) row_carrier_vec)
              then have "(of_int ((i - nr) + 2) - of_int ((j - nr) + 2)) * row A 0 $ l =  0\<^sub>v n $ l"
                by (metis \<open>(of_int (int (i - nr + 2)) - of_int (int (j - nr + 2))) \<cdot>\<^sub>v row A 0 = 0\<^sub>v n\<close>)
              then have "(of_int ((i - nr) + 2) - of_int ((j - nr) + 2)) * row A 0 $ l = 0"
                by (metis \<open>l < n \<and> row A 0 $ l \<noteq> 0\<close> index_zero_vec(1))
              then have "(of_int ((i - nr) + 2) - of_int ((j - nr) + 2)) = 0" 
                by (metis \<open>l < n \<and> row A 0 $ l \<noteq> 0\<close> cancel_comm_monoid_add_class.diff_cancel mult_eq_0_iff of_int_eq_iff r_right_minus_eq)

              then show ?thesis 
                by (smt (verit, best) \<open>nr \<le> i\<close> \<open>nr \<le> j\<close> add_right_cancel i_j le_add_diff_inverse of_int_of_nat_eq of_nat_eq_iff)
            qed
          qed
        qed
      qed
      have "distinct (cols ?fullA)" 
        by (metis \<open>distinct (cols A)\<close> assms(1) gfgd mat_carrier mat_of_rows_def)
      have "lin_dep (set (rows ?fullA))"
      proof -
        have "row ?fullA nr = row ?app_rows 0" 
          by (smt (verit, ccfv_threshold) True \<open>mat_of_rows n (map (\<lambda>k. (of_int k + 2) \<cdot>\<^sub>v row A 0) (map int [0..<n - nr])) \<in> carrier_mat (n - nr) n\<close> \<open>nr \<le> n\<close> append_rows_nth(2) assms(1) cancel_comm_monoid_add_class.diff_cancel le_add_diff_inverse verit_comp_simplify1(2))
        have "row ?app_rows 0 = (map (\<lambda>k. (of_int k + 2) \<cdot>\<^sub>v row A 0) (map int [0..<n - nr])) ! 0" 
          using True assms(1) `nr > 0` by fastforce
        then have "row ?app_rows 0 = 2 \<cdot>\<^sub>v row A 0" 
          by (simp add: True)
        then have "row ?fullA nr = 2 \<cdot>\<^sub>v row A 0" 
          using \<open>row (A @\<^sub>r mat_of_rows n (map (\<lambda>k. (of_int k + 2) \<cdot>\<^sub>v row A 0) (map int [0..<n - nr]))) nr = row (mat_of_rows n (map (\<lambda>k. (of_int k + 2) \<cdot>\<^sub>v row A 0) (map int [0..<n - nr]))) 0\<close> by presburger
        have "row ?fullA 0 = row A 0" 
          using \<open>mat_of_rows n (map (\<lambda>k. (of_int k + 2) \<cdot>\<^sub>v row A 0) (map int [0..<n - nr])) \<in> carrier_mat (n - nr) n\<close> append_rows_nth(1) assms(1) `nr > 0` by blast
        then have "row ?fullA nr = 2 \<cdot>\<^sub>v row ?fullA 0" using `row ?fullA nr = 2 \<cdot>\<^sub>v row A 0` by auto
        then show ?thesis using dasdasd[of ?fullA n nr 0 2] 
          using True sq_fullA by linarith
      qed
      then have "lin_dep (set (cols ?fullA))" using lin_dep_cols_iff_rows[of ?fullA] 
        using \<open>A @\<^sub>r mat_of_rows n (map (\<lambda>k. (of_int k + 2) \<cdot>\<^sub>v row A 0) (map int [0..<n - nr])) \<in> carrier_mat n n\<close> \<open>distinct (cols (A @\<^sub>r mat_of_rows n (map (\<lambda>k. (of_int k + 2) \<cdot>\<^sub>v row A 0) (map int [0..<n - nr]))))\<close> \<open>distinct (rows (A @\<^sub>r mat_of_rows n (map (\<lambda>k. (of_int k + 2) \<cdot>\<^sub>v row A 0) (map int [0..<n - nr]))))\<close> by fastforce

      obtain v where "v \<in> carrier_vec n" "v \<noteq> 0\<^sub>v n" "?fullA *\<^sub>v v = 0\<^sub>v n" 
        using lin_depE1[of ?fullA] 
        using \<open>A @\<^sub>r mat_of_rows n (map (\<lambda>k. (of_int k + 2) \<cdot>\<^sub>v row A 0) (map int [0..<n - nr])) \<in> carrier_mat n n\<close> \<open>distinct (cols (A @\<^sub>r mat_of_rows n (map (\<lambda>k. (of_int k + 2) \<cdot>\<^sub>v row A 0) (map int [0..<n - nr]))))\<close> \<open>lin_dep (set (cols (A @\<^sub>r mat_of_rows n (map (\<lambda>k. (of_int k + 2) \<cdot>\<^sub>v row A 0) (map int [0..<n - nr])))))\<close> by blast
      then have "(A @\<^sub>r ?app_rows) *\<^sub>v v = A *\<^sub>v v @\<^sub>v ?app_rows *\<^sub>v v"
        by (metis assms(1) mat_carrier mat_mult_append mat_of_rows_def)
      have "A *\<^sub>v v = 0\<^sub>v nr" using append_rows_eq 
        by (smt (verit, ccfv_SIG) \<open>(A @\<^sub>r mat_of_rows n (map (\<lambda>k. (of_int k + 2) \<cdot>\<^sub>v row A 0) (map int [0..<n - nr]))) *\<^sub>v v = 0\<^sub>v n\<close> \<open>(A @\<^sub>r mat_of_rows n (map (\<lambda>k. (of_int k + 2) \<cdot>\<^sub>v row A 0) (map int [0..<n - nr]))) *\<^sub>v v = A *\<^sub>v v @\<^sub>v mat_of_rows n (map (\<lambda>k. (of_int k + 2) \<cdot>\<^sub>v row A 0) (map int [0..<n - nr])) *\<^sub>v v\<close> \<open>A @\<^sub>r mat_of_rows n (map (\<lambda>k. (of_int k + 2) \<cdot>\<^sub>v row A 0) (map int [0..<n - nr])) \<in> carrier_mat n n\<close> \<open>v \<in> carrier_vec n\<close> assms(1) mat_carrier mat_of_rows_def minus_cancel_vec mult_mat_vec_carrier mult_minus_distrib_mat_vec)

      obtain x where "x \<in> carrier_vec n \<and> A *\<^sub>v x = b" using assms(3) by auto
      have "x + v \<noteq> x" 
        by (simp add: \<open>v \<in> carrier_vec n\<close> \<open>v \<noteq> 0\<^sub>v n\<close> \<open>x \<in> carrier_vec n \<and> A *\<^sub>v x = b\<close>)
      have "A *\<^sub>v (x + v) = b"
      proof -
        have "A *\<^sub>v (x + v) = A *\<^sub>v x + A *\<^sub>v v" 
          using \<open>v \<in> carrier_vec n\<close> \<open>x \<in> carrier_vec n \<and> A *\<^sub>v x = b\<close> assms(1) mult_add_distrib_mat_vec by blast
        then show ?thesis 
          by (simp add: \<open>A *\<^sub>v v = 0\<^sub>v nr\<close> \<open>x \<in> carrier_vec n \<and> A *\<^sub>v x = b\<close> b)
      qed
      then have False 
        by (metis M.add.m_closed \<open>v \<in> carrier_vec n\<close> \<open>x + v \<noteq> x\<close> \<open>x \<in> carrier_vec n \<and> A *\<^sub>v x = b\<close> assms(3))
      then show ?thesis 
        by simp
    qed
  next
    case False
    then show ?thesis 
      by (simp add: \<open>nr \<le> n\<close> nless_le)
  qed

qed


lemma bounded_min_faces_are_vertexdfrgegegeg:
  fixes A :: "'a  mat"
  fixes bound:: "'a" 
  assumes A: "A \<in> carrier_mat nr n"
  assumes b: "b \<in> carrier_vec nr"
  defines "P \<equiv> polyhedron A b"
  assumes "P \<noteq> {}"
  assumes bounded: "\<forall> x \<in> P. \<forall> i < n.  x $ i \<le> bound" 
  assumes "min_face P F"
  assumes "dim_vec b' = Min {dim_vec d | C d I'.  F = {x. x \<in> carrier_vec n \<and> C *\<^sub>v x = d} \<and> 
          (C, d) = sub_system A b I'}"
  assumes " F = {x. x \<in> carrier_vec n \<and> A' *\<^sub>v x = b'}"  
  assumes "(A', b') = sub_system A b I"
  shows "dim_row A' = n"
proof -
  have "card F = 1" using bounded_min_faces_are_vertex assms(1-6) 
    by blast
  then have " \<exists>!x. x \<in> F" using card_eq_Suc_0_ex1 
    by (metis One_nat_def)
  then have "\<exists>!x. x \<in> carrier_vec n \<and> A' *\<^sub>v x = b'" using assms(8) 
    by auto
  have "lin_indpt (set (rows A'))" using vntero[of A nr b F b' A' I] 
    using A P_def assms(4) assms(6) assms(7) assms(8) assms(9) b by fastforce
  have "distinct (rows A')" using vnvnvnoo
    using A P_def assms(4) assms(6) assms(7) assms(8) assms(9) b 
    by blast
  have "A' \<in> carrier_mat (dim_row A') n" 
    by (metis A  assms(9) b carrier_matD(1) carrier_matD(2) carrier_mat_subsyst carrier_vecD  fst_conv)
  have "b' \<in> carrier_vec (dim_row A')" 
    by (metis \<open>A' \<in> carrier_mat (dim_row A') n\<close> \<open>\<exists>!x. x \<in> carrier_vec n \<and> A' *\<^sub>v x = b'\<close> mult_mat_vec_carrier)
  then show "dim_row A' = n" using lin_depE1assd[of A' "dim_row A'" b']  
    using  \<open>A' \<in> carrier_mat (dim_row A') n\<close> \<open>\<exists>!x. x \<in> carrier_vec n \<and> A' *\<^sub>v x = b'\<close> \<open>distinct (rows A')\<close> \<open>lin_indpt (set (rows A'))\<close> by blast
qed

lemma minus_mult_minus_one:
  fixes v :: "'a vec" 
  shows "- v = - 1 \<cdot>\<^sub>v v"
  unfolding smult_vec_def
proof
  show "dim_vec (- v) = dim_vec (vec (dim_vec v) (\<lambda>i. - 1 * v $ i))" 
    by simp
  fix i
  assume "i < dim_vec (vec (dim_vec v) (\<lambda>i. - 1 * v $ i))"
  have "(- v) $ i = - (v $ i)" 
    using \<open>i < dim_vec (vec (dim_vec v) (\<lambda>i. - 1 * v $ i))\<close> by force
  have "- (v $ i) = - 1 * v $ i" 
    by simp
  show " (- v) $ i = vec (dim_vec v) (\<lambda>i. - 1 * v $ i) $ i" 
    by (metis \<open>(- v) $ i = - v $ i\<close> \<open>- v $ i = - 1 * v $ i\<close> \<open>i < dim_vec (vec (dim_vec v) (\<lambda>i. - 1 * v $ i))\<close> dim_vec index_vec)
qed

lemma vnnv0w:
fixes x y:: "'a vec" 
  assumes "x \<in> carrier_vec n"
  assumes "y \<in> carrier_vec n"
  assumes "a \<in> carrier_vec n"
  assumes "b \<in> carrier_vec n"
  assumes "x \<le> a"
  assumes "y \<le> b"
  shows "x + y \<le> a + b" 
  by (metis assms(3) assms(4) assms(5) assms(6) carrier_vecD vec_add_mono)
    

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
  assumes AI: "A \<in> \<int>\<^sub>m"
  assumes bI: "b \<in> \<int>\<^sub>v"
  assumes "integer_hull P \<noteq> {}"
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
  then obtain y where y: "y \<in> carrier_vec n \<and> A *\<^sub>v y \<ge> 0\<^sub>v nr \<and> y \<bullet> row C j < 0" 
    using leI by blast

  have "y \<noteq> 0\<^sub>v n"
  proof
    assume "y = 0\<^sub>v n"
    then have "y \<bullet> row C j = 0" 
      using assms(7) row_carrier scalar_prod_left_zero by blast
    then show False using y 
      by linarith
  qed
  have "n \<noteq> 0"
  proof
    assume "n=0"
    then have "y = 0\<^sub>v 0" 
      using carrier_vecD vec_of_dim_0 y by blast
    then show False using `y \<noteq> 0\<^sub>v n` 
      using \<open>n = 0\<close> by blast
  qed
  then have "set\<^sub>v y \<noteq> {}" 
    by (metis carrier_vecD equals0D not_gr_zero vec_setI y)
  have "Max (abs ` (vec_set y)) > 0"
  proof(rule ccontr)
    assume "\<not> 0 < Max (abs ` set\<^sub>v y)"
    have "\<forall> y' \<in> (abs ` set\<^sub>v y). y' \<ge> 0" 
      by fastforce
    have "finite (abs ` set\<^sub>v y)" 
      by fastforce
    have "(abs ` set\<^sub>v y) \<noteq> {}" 
      using \<open>set\<^sub>v y \<noteq> {}\<close> by blast
    then have " Max (abs ` set\<^sub>v y) \<ge> 0" 
      by (meson Max_in \<open>\<forall>y'\<in>abs ` set\<^sub>v y. 0 \<le> y'\<close> \<open>finite (abs ` set\<^sub>v y)\<close>)
    then have "Max (abs ` (vec_set y)) = 0" 
      using \<open>\<not> 0 < Max (abs ` set\<^sub>v y)\<close> by linarith
    then have "\<forall> y' \<in> (abs ` set\<^sub>v y). y' = 0" 
      by (metis Max_ge \<open>\<forall>y'\<in>abs ` set\<^sub>v y. 0 \<le> y'\<close> \<open>finite (abs ` set\<^sub>v y)\<close> order_antisym_conv)
    then have "\<forall>y' \<in> set\<^sub>v y. y' = 0" 
      by auto
    then have "y = 0\<^sub>v n" unfolding zero_vec_def 
      by (metis M.zero_closed \<open>y \<noteq> 0\<^sub>v n\<close> carrier_vecD eq_vecI index_zero_vec(1) vec_setI y)
    then show False 
      using \<open>y \<noteq> 0\<^sub>v n\<close> by auto
  qed

   let ?y' = " (1/Max (abs ` (vec_set y))) \<cdot>\<^sub>v (- y)" 
  let ?fullA = "- A @\<^sub>r (1\<^sub>m n) @\<^sub>r (- 1\<^sub>m n)"
  let ?fullb = "0\<^sub>v nr @\<^sub>v 1\<^sub>v n @\<^sub>v 1\<^sub>v n" 
  let ?c = "row C j"
  let ?P' = "polyhedron ?fullA ?fullb"

  have 2:"?fullA \<in> carrier_mat (nr+2*n) n" 
    by (metis A carrier_append_rows mult_2 one_carrier_mat uminus_carrier_iff_mat)
  have 3:"?fullb \<in> carrier_vec (nr+2*n)" 
    by (simp add: mult_2)
  have "?y' \<in> ?P'" sorry
  then have 1:"?P' \<noteq> {}" by auto
  have "\<exists> x \<in> carrier_vec n. ?fullA *\<^sub>v x \<le> ?fullb" using `?y' \<in> ?P'`
    unfolding polyhedron_def by auto
  have  "\<forall> x \<in> ?P'. \<forall> i < n.  x $ i \<le> 1" sorry

  then have "\<exists> bnd. \<forall> x \<in> carrier_vec n. ?fullA *\<^sub>v x \<le> ?fullb \<longrightarrow> ?c \<bullet> x \<le> bnd" 
    unfolding polyhedron_def sorry
   then have 4:"has_Maximum {?c \<bullet> x | x. x \<in> carrier_vec n \<and> ?fullA *\<^sub>v x \<le> ?fullb}"
    using strong_duality_theorem_primal_sat_bounded_min_max[of ?fullA "nr+2*n" n ?fullb ?c]
    using 2 3 assms(7) row_carrier `\<exists> x \<in> carrier_vec n. ?fullA *\<^sub>v x \<le> ?fullb` 
    by blast 

  then obtain \<beta> where beta: "\<beta> = Maximum {?c \<bullet> x | x. x \<in> carrier_vec n \<and> ?fullA *\<^sub>v x \<le> ?fullb}"
    by auto
  then have 4:"support_hyp ?P' ?c \<beta>" unfolding support_hyp_def  
    by (smt (verit, best) Collect_cong 4 assms(7) mem_Collect_eq polyhedron_def row_carrier)
  let ?F = " ?P' \<inter> {x |x. ?c \<bullet> x = \<beta>}"
  have "face ?P' ?F" unfolding face_def using 1 4 
    by blast 
  then obtain F where F_def:"min_face ?P' F \<and> F \<subseteq> ?F" 
    using 2 3 face_contains_min_face[of ?fullA "nr+2*n" ?fullb ?F] 
    by blast
  then obtain z where "z \<in> F" 
    by (metis ex_in_conv face_non_empty gram_schmidt.min_face_elim(1))
  obtain A' b' I where A'_b':" F = {x. x \<in> carrier_vec n \<and> A' *\<^sub>v x = b'}"
    "(A', b') = sub_system ?fullA ?fullb I" 
    "dim_vec b' = Min {dim_vec d| C d I. (C, d) = sub_system ?fullA ?fullb I \<and> 
                                             F = {x. x \<in> carrier_vec n \<and> C *\<^sub>v x = d}}"
    using F_def vnvnvn[of ?fullA "(nr + 2*n)" ?fullb F]  
    using 2 3
    by (smt (verit, ccfv_SIG))
  have "dim_row A' = n" using bounded_min_faces_are_vertexdfrgegegeg[of ?fullA "nr+ 2*n" ?fullb 1 F b' A' I]
    using A'_b' `\<forall> x \<in> ?P'. \<forall> i < n.  x $ i \<le> 1` 1 2 3 
    by (smt (verit, ccfv_SIG) Collect_cong F_def)
   then have "A' \<in> carrier_mat n n" 
     by (metis "2" A'_b'(2) carrier_matD(2) carrier_matI dim_col_subsyst_mat fst_conv)
  then have "lin_indpt (set (rows A'))" using vntero[of ?fullA "(nr + 2*n)" ?fullb F] 1 
    using 2 3 F_def 
    by (smt (verit, best) A'_b'(1) A'_b'(2) A'_b'(3) Collect_cong)
  have "distinct (rows A')" using vnvnvnoo[of ?fullA "(nr + 2*n)" ?fullb F b' A'] 1 
    using 2 3 F_def
    by (smt (verit, del_insts) A'_b'(1) A'_b'(2) A'_b'(3) Collect_cong)
  have "(rows A') = cols (A'\<^sup>T)" 
    by simp

  have "lin_indpt (set (cols A'\<^sup>T))" using `lin_indpt (set (rows A'))` by auto
  have "distinct (cols A'\<^sup>T)" using `distinct (rows A')` by auto
  have "A' \<in> carrier_mat (dim_row A') n" 
    by (metis A'_b'(2) 2 carrier_matD(2) carrier_matI dim_col_subsyst_mat fst_conv)
  then have "rank A'\<^sup>T = dim_row A'" 
    using lin_indpt_full_rank[of "A'\<^sup>T" "dim_row A'"] `lin_indpt (set (cols A'\<^sup>T))` `distinct (cols A'\<^sup>T)`
    using transpose_carrier_mat by blast
  then have "det A' \<noteq> 0" 
    by (metis \<open>A' \<in> carrier_mat (dim_row A') n\<close> \<open>dim_row A' = n\<close> det_rank_iff det_transpose transpose_carrier_mat)


  have "A' *\<^sub>v z = b \<longleftrightarrow> z = vec n (\<lambda> k. det (replace_col A' b k) / det A')" sorry

  have "det A \<in> \<int>" using Ints_det AI 
    using Ints_mat_def by blast

  let ?z' = "- abs(det A') \<cdot>\<^sub>v z" 
  have "?z' \<in> \<int>\<^sub>v" sorry

   

   
    have "?c \<bullet> ?y' =  (- 1 / Max (abs ` set\<^sub>v y)) * (?c \<bullet>  y)" 
      using y assms(7) row_carrier scalar_prod_smult_distrib 
      by force
    have "(1 / Max (abs ` set\<^sub>v y)) > 0" 
      using \<open>0 < Max (abs ` set\<^sub>v y)\<close> zero_less_divide_1_iff by blast
    then have "?c \<bullet> ?y' > 0" using y 
      by (metis (no_types, lifting) "4" \<open>0 < Max (abs ` set\<^sub>v y)\<close> \<open>row C j \<bullet> (1 / Max (abs ` set\<^sub>v y) \<cdot>\<^sub>v - y) = - 1 / Max (abs ` set\<^sub>v y) * (row C j \<bullet> y)\<close>  comm_scalar_prod divide_cancel_left gram_schmidt.support_hyp_def le_minus_one_simps(3) le_numeral_extra(3) linorder_not_le  nonzero_mult_div_cancel_right zero_le_divide_iff)
    have "\<beta> \<ge> ?c \<bullet> ?y'" using `?y' \<in> ?P'` unfolding polyhedron_def  
        using beta 
        using "4" \<open>1 / Max (abs ` set\<^sub>v y) \<cdot>\<^sub>v - y \<in> polyhedron (- A @\<^sub>r 1\<^sub>m n @\<^sub>r - 1\<^sub>m n) (0\<^sub>v nr @\<^sub>v 1\<^sub>v n @\<^sub>v 1\<^sub>v n)\<close> gram_schmidt.support_hyp_is_valid(1) by blast
      then have "\<beta> > 0" 
        using \<open>0 < row C j \<bullet> (1 / Max (abs ` set\<^sub>v y) \<cdot>\<^sub>v - y)\<close> order_less_le_trans by blast
       have "z \<in> carrier_vec n" 
        using A'_b'(1) \<open>z \<in> F\<close>  by force
      have "z \<in> ?F" 
        using F_def \<open>z \<in> F\<close> by blast
     
       then have "- A *\<^sub>v z \<le> 0\<^sub>v nr" unfolding polyhedron_def 
        using append_rows_le[of "-A" nr n "1\<^sub>m n @\<^sub>r - 1\<^sub>m n" "2*n" "0\<^sub>v nr" z "1\<^sub>v n @\<^sub>v 1\<^sub>v n"]
        by (simp add: A mult_2 )
    
      then have "- (A *\<^sub>v z) \<le> 0\<^sub>v nr" 
        using A A'_b'(1) \<open>z \<in> F\<close> by force


       then have "(-1) \<cdot>\<^sub>v (A *\<^sub>v z) \<le> 0\<^sub>v nr" using minus_mult_minus_one  
         by force
       then have "(abs(det A')) \<cdot>\<^sub>v ((-1) \<cdot>\<^sub>v (A *\<^sub>v z)) \<le> 0\<^sub>v nr" 
         using abs_ge_zero smult_nneg_npos_vec by blast
       then have "(abs(det A')*(-1)) \<cdot>\<^sub>v (A *\<^sub>v z) \<le> 0\<^sub>v nr" 
         by (metis smult_smult_assoc)
      then have "(- abs(det A')) \<cdot>\<^sub>v (A *\<^sub>v z) \<le> 0\<^sub>v nr" 
        by algebra
      then have "A *\<^sub>v ?z' \<le> 0\<^sub>v nr" using mult_mat_vec[of A nr n z "(- abs(det A'))"]
        using A A'_b'(1) \<open>z \<in> F\<close> by force


        have "row C j \<in> carrier_vec n" 
          using assms(7) row_carrier by blast
        have "\<forall> \<alpha> \<in> carrier_vec n. has_Maximum { \<alpha> \<bullet> x | x. x \<in> polyhedron C d} \<longrightarrow>
   (\<exists>x. x \<in> polyhedron C d \<and> \<alpha> \<bullet> x = Maximum { \<alpha> \<bullet> x | x. x \<in> polyhedron C d}  \<and> x \<in> \<int>\<^sub>v)" 
        proof -
          have "polyhedron C d = integer_hull (polyhedron C d)" 
            by (metis (no_types, lifting) P_def assms(5) gram_schmidt.polyhedron_def integer_hull_is_integer_hull mem_Collect_eq subset_iff)
          then have "(\<forall> F. face (polyhedron C d) F \<longrightarrow> (\<exists> x \<in> F. x \<in> \<int>\<^sub>v))"
            using P_int_then_face_int 
            by (metis A AI P_def assms(5) b bI integer_hull_of_polyhedron)
          then show ?thesis using int_face_then_max_suphyp_int[of C _ d] 
            by (smt (z3) A AI Collect_cong P_def assms(5) b bI int_face_then_max_suphyp_int integer_hull_of_polyhedron)
        qed
        then obtain v where v:"v \<in> polyhedron C d \<and> ?c \<bullet> v = Maximum { ?c \<bullet> x | x. x \<in> polyhedron C d}  \<and> v \<in> \<int>\<^sub>v" 
          using assms(8) `row C j \<in> carrier_vec n` 
          by meson
    
   
      
      then have "v \<in> integer_hull P" using assms(5) 
        by blast 
      then have "v \<in> P" sorry

        have "A *\<^sub>v v \<le> b" using `v \<in> P` unfolding P_def polyhedron_def by auto
        have "v \<in> carrier_vec n" using v unfolding P_def polyhedron_def by auto
        have "?z' \<in> carrier_vec n" using `z \<in> carrier_vec n` 
          by blast 
      have "\<forall> m::nat. v + of_int m \<cdot>\<^sub>v ?z' \<in> P"
      proof
        fix m::nat
        
        have " m \<ge> 0" 
          by simp 
        have "A *\<^sub>v (of_int m \<cdot>\<^sub>v ?z') = of_int m \<cdot>\<^sub>v ( A *\<^sub>v ?z')" 
          using mult_mat_vec[of A nr n z "of_int m"]  using A A'_b'(1) \<open>z \<in> F\<close> by force
        have "of_int m \<cdot>\<^sub>v ( A *\<^sub>v ?z') \<le> 0\<^sub>v nr" 
            using smult_nneg_npos_vec[of "of_int m" "A *\<^sub>v ?z'" nr] 
            by (simp add:  ` m \<ge> 0` `A *\<^sub>v ?z' \<le> 0\<^sub>v nr`)
          then have "A *\<^sub>v (of_int m \<cdot>\<^sub>v ?z') \<le> 0\<^sub>v nr" 
            using `A *\<^sub>v (of_int m \<cdot>\<^sub>v ?z') = of_int m \<cdot>\<^sub>v ( A *\<^sub>v ?z')` by auto
          have "v + of_int m \<cdot>\<^sub>v ?z' \<in> carrier_vec n" 
            using \<open>- \<bar>det A'\<bar> \<cdot>\<^sub>v z \<in> carrier_vec n\<close> \<open>v \<in> carrier_vec n\<close> by blast
          have "A *\<^sub>v (v + of_int m \<cdot>\<^sub>v ?z') = A *\<^sub>v v + A *\<^sub>v (of_int m \<cdot>\<^sub>v ?z')" 
            by (meson A \<open>- \<bar>det A'\<bar> \<cdot>\<^sub>v z \<in> carrier_vec n\<close> \<open>v \<in> carrier_vec n\<close> mult_add_distrib_mat_vec smult_closed)
          have "A *\<^sub>v v + A *\<^sub>v (of_int m \<cdot>\<^sub>v ?z') \<le> b + 0\<^sub>v nr"
            using `A *\<^sub>v v \<le> b` `A *\<^sub>v (of_int m \<cdot>\<^sub>v ?z') \<le> 0\<^sub>v nr` using vec_add_mono 
            by (metis b carrier_vecD index_zero_vec(2))
          then have "A *\<^sub>v (v + of_int m \<cdot>\<^sub>v ?z') \<le> b" 
            by (metis \<open>A *\<^sub>v (v + of_int (int m) \<cdot>\<^sub>v (- \<bar>det A'\<bar> \<cdot>\<^sub>v z)) = A *\<^sub>v v + A *\<^sub>v (of_int (int m) \<cdot>\<^sub>v (- \<bar>det A'\<bar> \<cdot>\<^sub>v z))\<close> b right_zero_vec)
          then show "v + of_int (int m) \<cdot>\<^sub>v (- \<bar>det A'\<bar> \<cdot>\<^sub>v z) \<in> P"
            unfolding P_def polyhedron_def 
            using \<open>v + of_int (int m) \<cdot>\<^sub>v (- \<bar>det A'\<bar> \<cdot>\<^sub>v z) \<in> carrier_vec n\<close> by blast
        qed
        have "\<forall> m::nat. v + of_int m \<cdot>\<^sub>v ?z' \<in> \<int>\<^sub>v"
        proof
          fix m::nat
          have " m \<in> \<int>"  by simp 
          then have "of_int m \<cdot>\<^sub>v ?z' \<in> \<int>\<^sub>v" using int_mult_int_vec 
            using Ints_of_int \<open>- \<bar>det A'\<bar> \<cdot>\<^sub>v z \<in> \<int>\<^sub>v\<close> by blast
          then show "v + of_int m \<cdot>\<^sub>v ?z' \<in> \<int>\<^sub>v" using v 
            using \<open>- \<bar>det A'\<bar> \<cdot>\<^sub>v z \<in> carrier_vec n\<close> \<open>v \<in> carrier_vec n\<close> gram_schmidt.sum_int_is_int by blast
        qed
        then have "\<forall> m::nat. v + of_int m \<cdot>\<^sub>v ?z' \<in> integer_hull P" 
          by (metis A Diff_iff P_def \<open>\<forall>x. v + of_int (int x) \<cdot>\<^sub>v (- \<bar>det A'\<bar> \<cdot>\<^sub>v z) \<in> P\<close> b gram_schmidt.not_in_int_hull_not_int)



  
  oops
  then have "det A' \<noteq> 0" 

    oops
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
    then have "has_Maximum { row A i \<bullet> x | x. x \<in> P}" using eq_in_P_has_max 
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
    then obtain j where "j<nr' \<and> row C j \<bullet> y > d $ j" using y exists_eq_in_P_for_outside_elem [of C nr' d y] C_d  
        `y \<in> carrier_vec n` 
      by blast
    let ?\<alpha> = "row C j"
    let ?\<beta> = "d $ j"
    have " has_Maximum { ?\<alpha> \<bullet> x | x. x \<in> polyhedron C d}" 
      using eq_in_P_has_max[of C nr' d j] `integer_hull P \<noteq> {}` 
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
