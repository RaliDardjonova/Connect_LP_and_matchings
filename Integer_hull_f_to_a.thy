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
  fixes b:: "'a vec" 
  assumes A: "A \<in> carrier_mat nr n"
  assumes b: "b \<in> carrier_vec nr"
  defines "P \<equiv> polyhedron A b"
  assumes "P \<noteq> {}"
  assumes "min_face P F"
  obtains A' b' I where " F \<subseteq> P \<and> F \<noteq> {} \<and>
            dim_vec b' = Min {dim_vec d | C d I'.  
            F = {x. x \<in> carrier_vec n \<and> C *\<^sub>v x = d} \<and>  (C, d) = sub_system A b I'} \<and>
            F = {x. x \<in> carrier_vec n \<and> A' *\<^sub>v x = b'} \<and> (A', b') = sub_system A b I" 
  sorry


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
  assumes "b' \<noteq> 0\<^sub>v (dim_vec b')"
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

 obtain C d where "(C, d) = sub_system A b (I - {i})"
    by (metis surj_pair)
  have "{x.  A' *\<^sub>v x = b'} = {x.  C *\<^sub>v x = d \<and> row A i \<bullet> x = b $ i }"
    using remove_index_sub_system_eq[of A b i I A' b' C d] 
    by (metis A \<open>(C, d) = sub_system A b (I - {i})\<close> i assms(8) b carrier_matD(1) carrier_vecD)

    obtain  U a where U_a:"u = lincomb a U \<and> finite U \<and> U \<subseteq> set (rows A') - {u}" 
    unfolding span_def using 1   
    using in_spanE u by presburger
 
  obtain Ul where "set Ul = U" 
    by (meson U_a finite_list)
  then obtain c where "u = lincomb_list c Ul" using pojopp[of Ul u a] 
    by (metis Diff_iff U_a \<open>set (rows A') \<subseteq> carrier_vec n\<close> subset_eq)
  


  
  then have 2:"u = sumlist (map (\<lambda>i. c i \<cdot>\<^sub>v  Ul ! i) [0..<length Ul])"
    using lincomb_list_def by presburger
  have 3:"(\<And>v. v \<in> set ((map (\<lambda>i. c i \<cdot>\<^sub>v  Ul ! i) [0..<length Ul])) \<Longrightarrow> v \<in> carrier_vec n)"
    by (smt (z3) U_a \<open>set (rows A') \<subseteq> carrier_vec n\<close> \<open>set Ul = U\<close> add_cancel_left_left in_set_conv_nth insert_Diff_single insert_absorb2 insert_subset length_map map_eq_conv map_nth mk_disjoint_insert nth_upt smult_closed subset_eq u)
  have "U \<subseteq> set (rows C)" sorry

  have "\<forall>x \<in> carrier_vec n.  C *\<^sub>v x = d \<longrightarrow> row A i \<bullet> x = b $ i" 
  proof(safe)
    fix x
    assume "C *\<^sub>v x = d" 
    assume "x \<in> carrier_vec n" 
    then have "u \<bullet> x = sumlist (map (\<lambda>i. c i \<cdot>\<^sub>v  Ul ! i) [0..<length Ul]) \<bullet> x"
      using 2 by auto
    then have "u \<bullet> x = sum_list (map ((\<bullet>) x) (map (\<lambda>i. c i \<cdot>\<^sub>v  Ul ! i) [0..<length Ul]))"
      using scalar_prod_right_sum_distrib 3 `x \<in> carrier_vec n` 
      by (metis (no_types, lifting) "2" \<open>set (rows A') \<subseteq> carrier_vec n\<close> comm_scalar_prod subset_code(1) u)
    then have "u \<bullet> x = sum_list  (map (\<lambda>i. (c i \<cdot>\<^sub>v  Ul ! i) \<bullet> x) [0..<length Ul])"
      by (smt (verit, best) "3" \<open>x \<in> carrier_vec n\<close> comm_scalar_prod length_map map_eq_conv' nth_map nth_mem)



  oops
  then have "\<exists> u \<in> (set (rows A')).\<exists> c. u = lincomb c ((set (rows A')) - {u})" 
    sledgehammer

    oops


   have "(\<And>a. lincomb a (set (rows A')) = 0\<^sub>v n \<Longrightarrow> \<forall>v\<in>set (rows A'). a v = 0)"
  proof
    fix a v
    assume "lincomb a (set (rows A')) = 0\<^sub>v n" 
    assume " v \<in> set (rows A')" 
    show "a v = 0" 
      oops
  




    oops



  have "A' \<in> carrier_mat (dim_row A') n" using carrier_mat_subsyst[of A b I] 
    by (metis A assms(8) b carrier_matD(1) carrier_matD(2) carrier_vecD fst_conv)
  obtain v where "v \<in> carrier_vec (dim_row A')" "v \<noteq> 0\<^sub>v (dim_row A')" "A'\<^sup>T *\<^sub>v v = 0\<^sub>v n"
    using lin_depE[of "A'\<^sup>T" "dim_row A'"] cols_transpose[of A'] `distinct (rows A')` 
    by (metis \<open>A' \<in> carrier_mat (dim_row A') n\<close> \<open>lin_dep (set (rows A'))\<close> transpose_carrier_mat)
  obtain x where "x \<in> F" 
    using assms(5) unfolding min_face_def 
    by (metis ex_in_conv face_non_empty)
  then have "x \<in> carrier_vec n" 
    using assms(7) by blast
  have "(A'\<^sup>T *\<^sub>v v) \<bullet> x = v \<bullet> (A' *\<^sub>v x)"  using Move_To_Matrix.transpose_vec_mult_scalar
    using \<open>A' \<in> carrier_mat (dim_row A') n\<close> \<open>v \<in> carrier_vec (dim_row A')\<close> \<open>x \<in> carrier_vec n\<close> by blast
  then have " v \<bullet> (A' *\<^sub>v x) = 0" 
    using \<open>A'\<^sup>T *\<^sub>v v = 0\<^sub>v n\<close> \<open>x \<in> carrier_vec n\<close> by fastforce
  then have "v \<bullet> b' = 0" 
    using \<open>x \<in> F\<close> assms(7) by blast
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
