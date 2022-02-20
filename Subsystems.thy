theory Subsystems
  imports  Linear_Inequalities.Decomposition_Theorem 
          Jordan_Normal_Form.DL_Rank_Submatrix

begin 

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

lemma  dim_subsyst_vec_less_b:
  shows "dim_vec (snd (sub_system A b I)) \<le> dim_vec b"
proof -
  have "{i. i < dim_vec b \<and> i \<in> I} \<subseteq> {0..<dim_vec b}" by auto
  then have "card {i. i < dim_vec b \<and> i \<in> I} \<le> card  {0..<dim_vec b}" 
    by (metis card_mono finite_atLeastLessThan)
  then show ?thesis 
    by (metis card_atLeastLessThan diff_zero dim_subsyst_vec)
qed

lemma  dim_subsyst_mat_less_A:
  shows "dim_row (fst (sub_system A b I)) \<le> dim_row A"
proof -
  have "{i. i < dim_row A \<and> i \<in> I} \<subseteq> {0..<dim_row A}" by auto
  then have "card {i. i < dim_row A \<and> i \<in> I} \<le> card  {0..<dim_row A}" 
    by (metis card_mono finite_atLeastLessThan)
  then show ?thesis 
    by (metis card_atLeastLessThan diff_zero dim_row_subsyst_mat)
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

lemma nths_UNIV_same:
  "nths xs UNIV = xs"
  unfolding nths_def
proof -
  have "\<forall> p \<in> set ((zip xs [0..<length xs])). snd p \<in> UNIV" by blast
 
  then have "(filter (\<lambda>p. snd p \<in> UNIV) (zip xs [0..<length xs])) =
          (zip xs [0..<length xs])" 
    using filter_True by blast
  then show " map fst (filter (\<lambda>p. snd p \<in> UNIV) (zip xs [0..<length xs])) =  xs" 
    by simp
qed

lemma itself_is_subsyst:
 shows "(A, b) = sub_system A b UNIV" 
proof
  have "A = submatrix A UNIV UNIV"
    apply rule
      apply (simp add: dim_submatrix(1) dim_submatrix(2) pick_UNIV submatrix_index)
  proof-
    have "dim_row (submatrix A UNIV UNIV) = card {i. i<dim_row A \<and> i\<in>UNIV}"
      using  dim_submatrix(1) by blast
    then show " dim_row A = dim_row (submatrix A UNIV UNIV)" by simp
    have "dim_col (submatrix A UNIV UNIV) = card {i. i<dim_col A \<and> i\<in>UNIV}" 
      using  dim_submatrix(2) by fastforce
    then show "dim_col A = dim_col (submatrix A UNIV UNIV)"
      using  dim_submatrix(2) by simp
  qed
  
  then show "fst (A, b) = fst (sub_system A b UNIV)"
    by (metis fst_eqD sub_system_fst)
  have "(nths (list_of_vec b) UNIV) =  (list_of_vec b)" 
    using  nths_UNIV_same by auto  
  then have "b = vec_of_list (nths (list_of_vec b) UNIV)" 
    using  nths_UNIV_same by simp
  then show "snd (A, b) = snd (sub_system A b UNIV)" 
    by (simp add: sub_system_snd)
qed  

lemma pick_index_row_in_A:

  assumes "dim_row A = dim_vec b" 
 shows "\<forall> j < dim_vec (snd (sub_system A b I)). 
        row (fst (sub_system A b I)) j = row A (pick I j) \<and> (snd (sub_system A b I)) $ j = b $ (pick I j)"
proof(rule)
  fix j
 
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
  assumes "dim_row A = dim_vec b" 
 shows "\<forall> j < dim_vec (snd (sub_system A b I)). 
        \<exists> i < dim_vec b. i \<in> I \<and> row (fst (sub_system A b I)) j = row A i \<and> (snd (sub_system A b I)) $ j = b $ i"
proof(rule)
  fix j

  show " j < dim_vec (snd (sub_system A b I)) \<longrightarrow>
         (\<exists>i<dim_vec b. i \<in> I \<and> row (fst (sub_system A b I)) j = row A i \<and> snd (sub_system A b I) $ j = b $ i)"
  proof
    assume "j < dim_vec (snd (sub_system A b I))" 
    then have "j < card {i. i < dim_row A \<and> i \<in> I}" 
      using `dim_row A = dim_vec b`  
      by (metis  dim_subsyst_vec)
  
    have "(pick I j) < dim_vec b" 
      by (metis  \<open>j < dim_vec (snd (sub_system A b I))\<close>  dim_subsyst_vec pick_le)
    have "(pick I j) \<in> I" 
      apply(cases "finite I") 
       apply (metis (mono_tags, lifting) \<open>dim_row A = dim_vec b\<close> \<open>j < dim_vec (snd (sub_system A b I))\<close> dim_row_less_card_I dims_subsyst_same le_trans linorder_not_le pick_in_set_le)
      using pick_in_set_inf by auto

  then show " \<exists> i < dim_vec b. i \<in> I \<and> row (fst (sub_system A b I)) j = row A i \<and> (snd (sub_system A b I)) $ j = b $ i" 
    
    by (meson  \<open>j < dim_vec (snd (sub_system A b I))\<close> \<open>pick I j < dim_vec b\<close> `dim_row A = dim_vec b` pick_index_row_in_A)
qed
qed


lemma exist_index_in_A':
 
  assumes "dim_row A = dim_vec b"
 assumes "j < dim_vec b"
 assumes "j \<in> I"
 shows " \<exists> i < dim_vec (snd (sub_system A b I)).
       row (fst (sub_system A b I)) i = row A j \<and> (snd (sub_system A b I)) $ i = b $ j"
proof -
have "dim_vec (snd (sub_system A b I)) = card {i. i < dim_vec b \<and> i \<in> I}" 
    by (metis dim_subsyst_vec)
  have "pick I (card {a\<in>I. a < j}) = j" using pick_card_in_set assms(3) by auto
  have "{a\<in>I. a < j} \<subseteq> {i. i < dim_vec b \<and> i \<in> I}" using assms(2) by force
  then have "card {a\<in>I. a < j} \<le> card {i. i < dim_vec b \<and> i \<in> I}" 
    by (metis (no_types, lifting) card_mono finite_nat_set_iff_bounded_le less_le_not_le mem_Collect_eq)
  then have "card {a\<in>I. a < j} <  dim_vec (snd (sub_system A b I))" 
    by (metis (no_types, lifting) \<open>dim_vec (snd (sub_system A b I)) = card {i. i < dim_vec b \<and> i \<in> I}\<close> \<open>{a \<in> I. a < j} \<subseteq> {i. i < dim_vec b \<and> i \<in> I}\<close> assms(3) assms(2) card_seteq dual_order.irrefl finite_nat_set_iff_bounded_le less_imp_le_nat mem_Collect_eq order_neq_le_trans)
  have "row (fst (sub_system A b I)) (card {a\<in>I. a < j}) = row A j"
    using pick_index_row_in_A assms(1) 
    by (metis (no_types, lifting) \<open>card {a \<in> I. a < j} < dim_vec (snd (sub_system A b I))\<close> \<open>pick I (card {a \<in> I. a < j}) = j\<close>)
  have "(snd (sub_system A b I)) $  (card {a\<in>I. a < j})= b $ j"
    using pick_index_row_in_A assms(1-2) 
    by (metis (no_types, lifting) \<open>card {a \<in> I. a < j} < dim_vec (snd (sub_system A b I))\<close> \<open>pick I (card {a \<in> I. a < j}) = j\<close>)
  then show ?thesis 
    using \<open>card {a \<in> I. a < j} < dim_vec (snd (sub_system A b I))\<close> \<open>row (fst (sub_system A b I)) (card {a \<in> I. a < j}) = row A j\<close> by blast
qed

lemma subsystem_of_subsyst:
  assumes "J \<subseteq> I" 
  assumes "(A', b') = sub_system A b I" 
  assumes "(A'', b'') = sub_system A b J"
  shows "\<exists> I'. (A'', b'') = sub_system A' b' I'" 
  sorry

lemma subsystem_of_subsyst1:
 assumes "dim_row A = dim_vec b"
  assumes "(A', b') = sub_system A b I"
  assumes "\<forall> i < dim_row A'. P (row A' i) (b' $ i)"
  shows "\<forall>i \<in> I \<inter> {0..<dim_row A}. P (row A i) (b $ i)" 
proof 
  fix i
  assume "i \<in> I \<inter> {0..<dim_row A}" 
  have "dim_row A' = dim_vec b'" using assms(1) 
    by (metis assms(2) dims_subsyst_same prod.sel(1) prod.sel(2))
  then obtain j where "j<dim_row A' \<and> row A' j = row A i \<and> b' $ j = b $ i" 
    using exist_index_in_A'[of A b i I]  assms(1-2) 
    by (metis IntD1 IntD2 \<open>i \<in> I \<inter> {0..<dim_row A}\<close> atLeastLessThan_iff fst_conv snd_conv)
  then show "P (row A i) (b $ i)" using assms(3) by auto
qed

lemma subsystem_of_subsyst2:
 assumes "dim_row A = dim_vec b"
 assumes "(A', b') = sub_system A b I"
 assumes "\<forall>i \<in> I \<inter> {0..<dim_row A}. P (row A i) (b $ i)"
 shows "\<forall> i < dim_row A'. P (row A' i) (b' $ i)"
proof(rule)+
  fix i
  assume "i < dim_row A'"
  have "dim_row A' = dim_vec b'" using assms(1) 
    by (metis assms(2) dims_subsyst_same prod.sel(1) prod.sel(2))
  then obtain j where "j \<in> I \<and> j <dim_row A \<and> (row A j) = (row A' i) \<and> b $ j = b' $ i"
  using exist_index_in_A[of A b I] assms(1-2) `i < dim_row A'`
  by (metis fst_conv snd_conv) 
  then have "P (row A j) (b $ j)" using assms(3) 
    by (metis Int_iff atLeastLessThan_iff zero_le)
  then show " P (row A' i) (b' $ i)" 
    by (simp add: \<open>j \<in> I \<and> j < dim_row A \<and> row A j = row A' i \<and> b $ j = b' $ i\<close>)
qed

lemma insert_sub_system':
  assumes "dim_row A = dim_vec b"
  assumes "i \<notin> I" 
  assumes "i < dim_vec b" 
  assumes "(A', b') = sub_system A b I" 
  assumes "(A'', b'') = sub_system A b (I \<union> {i})"
  shows "(\<forall> i < dim_row A''. P (row A'' i) (b'' $ i)) \<longleftrightarrow>
         ( \<forall> j < dim_row A'. P (row A' j) (b' $ j)) \<and> P (row A i)  (b $ i)"
proof(safe)
    have "dim_vec b' = dim_row A'" using assms(1) 
      by (metis assms(4) dims_subsyst_same fst_conv snd_conv)
    {
      fix j
      assume "\<forall>i<dim_row A''. P (row A'' i) (b'' $ i)"
     then have "\<forall>i \<in> (I \<union> {i}) \<inter> {0..<dim_vec b}. P (row A i) (b $ i)" 
        using subsystem_of_subsyst1[of A b A'' b'' "(I \<union> {i})" P] 
        using \<open>\<forall>i<dim_row A''. P (row A'' i) (b'' $ i)\<close> assms(1) assms(5) by fastforce
      {assume "j < dim_row A'" 
     
      show "P (row A' j) (b' $ j)" 
        by (metis Int_iff Un_Int_eq(3) \<open>\<forall>i\<in>(I \<union> {i}) \<inter> {0..<dim_vec b}. P (row A i) (b $ i)\<close> \<open>j < dim_row A'\<close> assms(1) assms(4) subsystem_of_subsyst2)
    }
    show " P (row A i) (b $ i)" 
      by (simp add: \<open>\<forall>i\<in>(I \<union> {i}) \<inter> {0..<dim_vec b}. P (row A i) (b $ i)\<close> assms(3))
    }
    {  fix ia 
      assume as: "(\<forall>j<dim_row A'. P (row A' j) (b' $ j))" "P (row A i) (b $ i)" 
        "ia < dim_row A''"
    then have " P (row A i) (b $ i) \<and> i \<in> {0..<dim_vec b}" using assms(3) 
  using atLeastLessThan_iff by blast
    then have "\<forall>i \<in> I \<inter> {0..<dim_vec b}. P (row A i) (b $ i)" 
    using subsystem_of_subsyst1[of A b A' b' I P] as
    assms(1) assms(4) by auto
 
  then have "\<forall>i \<in> (I \<union> {i}) \<inter> {0..<dim_vec b}. P (row A i) (b $ i)" 
    using as assms(3)
  by blast
  then have "\<forall> i < dim_row A''. P (row A'' i) (b'' $ i)" using  assms(1) assms(5)
    subsystem_of_subsyst2[of A b A'' b'' "I \<union> {i}" "P"] 
    by presburger
  then show " P (row A'' ia) (b'' $ ia)" using as
      using  assms(1) assms(5) subsystem_of_subsyst2 
      by presburger
  }
qed
      

lemma insert_sub_system:
  assumes "dim_row A = dim_vec b"
  assumes "i \<notin> I" 
  assumes "i < dim_vec b" 
  assumes "(A', b') = sub_system A b I" 
  assumes "(A'', b'') = sub_system A b (I \<union> {i})"
  shows "{x. A'' *\<^sub>v x = b''} = {x. A' *\<^sub>v x = b' \<and> row A i \<bullet> x = b $ i}"
proof -
  have "\<forall>x.  A'' *\<^sub>v x = b'' \<longleftrightarrow>  A' *\<^sub>v x = b' \<and> row A i \<bullet> x = b $ i" 
  proof
    fix x
    have "(\<forall>i<dim_row A''. row A'' i \<bullet> x = b'' $ i) =
    ((\<forall>j<dim_row A'. row A' j \<bullet> x = b' $ j) \<and>
     row A i \<bullet> x = b $ i)"   
  using insert_sub_system'[of A b i I A' b' A'' b'' "(\<lambda> r y.   r \<bullet> x = y)"] assms by fast
  then show "A'' *\<^sub>v x = b'' \<longleftrightarrow>  A' *\<^sub>v x = b' \<and> row A i \<bullet> x = b $ i"
 unfolding mult_mat_vec_def using dim_vec 
  by (smt (verit, del_insts) assms(1) assms(4) assms(5) dims_subsyst_same eq_vecI index_vec prod.sel(1) prod.sel(2))
qed
  then show ?thesis by presburger
qed


lemma remove_index_sub_system':
assumes "dim_row A = dim_vec b" 
assumes "i \<notin> I"
assumes "i < dim_vec b"
  assumes "(A', b') = sub_system A b I" 
  assumes "(A'', b'') = sub_system A b (I \<union> {i})"
  shows "{x. A'' *\<^sub>v x \<le> b''} = {x. A' *\<^sub>v x \<le> b' \<and> row A i \<bullet> x \<le> b $ i}"
proof -
  have "\<forall>x.  A'' *\<^sub>v x \<le> b'' \<longleftrightarrow>  A' *\<^sub>v x \<le> b' \<and> row A i \<bullet> x \<le> b $ i" 
  proof
    fix x
    have "(\<forall>i<dim_row A''. row A'' i \<bullet> x \<le> b'' $ i) =
    ((\<forall>j<dim_row A'. row A' j \<bullet> x \<le> b' $ j) \<and>
     row A i \<bullet> x \<le> b $ i)"   
      using insert_sub_system'[of A b i I A' b' A'' b'' "(\<lambda> r y.   r \<bullet> x \<le> y)"] 
assms by fast 
  then show "A'' *\<^sub>v x \<le> b'' \<longleftrightarrow>  A' *\<^sub>v x \<le> b' \<and> row A i \<bullet> x \<le> b $ i"
    unfolding mult_mat_vec_def using dim_vec 
    assms(1) assms(4) assms(5) dims_subsyst_same index_vec prod.sel(1) prod.sel(2)
    by (smt (verit, del_insts) less_eq_vec_def)
qed
  then show ?thesis by presburger
qed

lemma remove_index_sub_system:
assumes "dim_row A = dim_vec b" 
assumes "i \<in> I"
assumes "i < dim_vec b"
  assumes "(A', b') = sub_system A b I" 
  assumes "(A'', b'') = sub_system A b (I - {i})"
  shows "{x. A' *\<^sub>v x \<le> b'} = {x. A'' *\<^sub>v x \<le> b'' \<and> row A i \<bullet> x \<le> b $ i}"
proof -
  have "i \<notin> (I - {i})" using assms(2) by auto
  moreover have "I = (I - {i}) \<union> {i}" using assms(2) by auto
  ultimately show ?thesis 
    using remove_index_sub_system'[of A b i  "I - {i}" A'' b'' A' b'] assms(1) assms(3-5)
    by argo
qed


lemma add_index_sub_system_dims:
  assumes "i \<notin> I"
  assumes "i < dim_vec b"
  assumes "(A', b') = sub_system A b I" 
  assumes "(A'', b'') = sub_system A b (I \<union> {i})"
  shows "dim_vec b'' = dim_vec b' + 1"
proof -
  have "dim_vec b' = card {i. i < dim_vec b \<and> i \<in> I}" 
    using dim_subsyst_vec using assms(3) 
    by (metis snd_conv)
  have "{i. i < dim_vec b \<and> i \<in> I} = {i. i < dim_vec b} \<inter> I" by auto
   have "dim_vec b'' = card {j. j < dim_vec b \<and> j \<in> (I \<union> {i})}" 
    using dim_subsyst_vec using assms(4) 
    by (metis snd_conv)
  then have "{j. j < dim_vec b \<and> j \<in> (I \<union> {i})} = 
      ({i. i < dim_vec b} \<inter> I) \<union> {i}" using assms(2) by auto
  then have "card {i. i < dim_vec b \<and> i \<in> I} + 1 = card {j. j < dim_vec b \<and> j \<in> (I \<union> {i})}"
    by (simp add: \<open>{i. i < dim_vec b \<and> i \<in> I} = {i. i < dim_vec b} \<inter> I\<close> assms(1))
  then show ?thesis 
    using \<open>dim_vec b' = card {i. i < dim_vec b \<and> i \<in> I}\<close> \<open>dim_vec b'' = card {j. j < dim_vec b \<and> j \<in> I \<union> {i}}\<close> by presburger
qed
lemma remove_index_sub_system_dims:
  assumes "i \<in> I"
 assumes "i < dim_vec b"
  assumes "(A', b') = sub_system A b I" 
  assumes "(A'', b'') = sub_system A b (I - {i})"
  shows "dim_vec b' = dim_vec b'' + 1"
proof -
 have "i \<notin> (I - {i})" using assms(2) by auto
  moreover have "I = (I - {i}) \<union> {i}" using assms(1) by auto
  ultimately show ?thesis 
    using add_index_sub_system_dims[of  i   "I - {i}" b A'' b'' A A' b'] assms(1-4)
    by argo
qed  


end