theory Tot_Unimod_graph
  imports Totally_Unimodular "../archive-of-graph-formalizations/Undirected_Graphs/Bipartite"
begin

context gram_schmidt_floor
begin

definition set_to_list :: "'b set \<Rightarrow> 'b list"
  where "set_to_list s = (SOME l. set l = s \<and> distinct l)"

lemma  set_set_to_list:
  "finite s \<Longrightarrow> set (set_to_list s) = s"
  unfolding set_to_list_def
  by (metis (mono_tags, lifting) finite_distinct_list someI)

lemma  set_set_to_list_distinct:
  "finite s \<Longrightarrow> distinct (set_to_list s)"
  unfolding set_to_list_def
  by (metis (mono_tags, lifting) finite_distinct_list someI)


definition edges_list :: "'b set set \<Rightarrow> ('b set) list" where
  "edges_list E = set_to_list E"

lemma edges_list_el_in_E:
  assumes "k < card E"
  shows "edges_list E ! k \<in> E"
proof -
  have "finite E" 
    by (metis assms(1) card.infinite not_less_zero)
  have "set (edges_list E) = E" 
    unfolding edges_list_def using set_set_to_list 
    using \<open>finite E\<close> by blast
  have "edges_list E ! k \<in> set (edges_list E)" 
    by (metis \<open>set (edges_list E) = E\<close> assms card_length not_less nth_mem order_trans_rules(23))
  show ?thesis 
    using \<open>edges_list E ! k \<in> set (edges_list E)\<close> \<open>set (edges_list E) = E\<close> by blast
qed

lemma distinct_edges_list:
  assumes "finite E" 
  shows "distinct (edges_list E)"
  unfolding edges_list_def
  using set_set_to_list_distinct assms 
  by blast

definition vertices_list :: "'b set set \<Rightarrow> 'b list" where
  "vertices_list E = set_to_list (Vs E)" 

lemma vert_list_el_in_VsE:
  assumes "k < card (Vs E)"
  shows "vertices_list E ! k \<in> Vs E"
proof -
  have "finite (Vs E)" 
    by (metis assms(1) card.infinite not_less_zero)
  have "set (vertices_list E) = Vs E" 
    unfolding vertices_list_def using set_set_to_list 
    using \<open>finite (Vs E)\<close> by blast
  then have "vertices_list E ! k \<in> set (vertices_list E)" 
    by (metis assms card_length not_less nth_mem order_trans_rules(23))
  then show ?thesis 
    using \<open>set (vertices_list E) = Vs E\<close> by blast
qed

lemma distinct_vert_list:
  assumes "finite (Vs E)" 
  shows "distinct (vertices_list E)"
  unfolding vertices_list_def
  using set_set_to_list_distinct assms 
  by blast

lemma diff_verts:
  assumes "i < card (Vs E)"
  assumes "j < card (Vs E)"
  assumes "i \<noteq> j"
  shows "vertices_list E ! i \<noteq> vertices_list E ! j"
proof -
  have "finite (Vs E)" 
    by (metis assms(1) card.infinite less_nat_zero_code)
  have "distinct (vertices_list E)" 
    by (simp add: \<open>finite (Vs E)\<close> distinct_vert_list)
  then show ?thesis 
    unfolding vertices_list_def
    by (metis \<open>finite (Vs E)\<close> assms distinct_card nth_eq_iff_index_eq set_set_to_list)
qed

definition insidence_mat :: "'b set set  \<Rightarrow> 'a mat" where 
  "insidence_mat E = mat (card (Vs E)) (card E) 
          (\<lambda>(i,j). if (vertices_list E) ! i \<in> (edges_list E) ! j then 1 else 0)"

lemma dim_col_insidence_mat:
  shows "dim_col (insidence_mat E) = card E" 
  unfolding insidence_mat_def by auto

lemma dim_row_insidence_mat:
  shows "dim_row (insidence_mat E) = (card (Vs E))" 
  unfolding insidence_mat_def by auto

lemma one_then_in_edge:
  assumes "i < card (Vs E)"
  assumes "j < card E"
  assumes "(insidence_mat E) $$ (i,j) = 1"
  shows "(vertices_list E) ! i \<in> (edges_list E) ! j"
  using assms 
proof -
  have "(insidence_mat E) $$ (i,j) = (if (vertices_list E) ! i \<in> (edges_list E) ! j then 1 else 0)"
    unfolding insidence_mat_def using assms(1-2) 
    by fastforce
  then show ?thesis
    using assms(3) field.one_not_zero by presburger
qed

lemma zeo_then_notin_edge:
  assumes "i < card (Vs E)"
  assumes "j < card E"
  assumes "(insidence_mat E) $$ (i,j) = 0"
  shows "(vertices_list E) ! i \<notin> (edges_list E) ! j"
  using assms 
proof -
  have "(insidence_mat E) $$ (i,j) = (if (vertices_list E) ! i \<in> (edges_list E) ! j then 1 else 0)"
    unfolding insidence_mat_def using assms(1-2) 
    by fastforce
  then show ?thesis
    using assms(3) field.one_not_zero 
    by presburger
qed  

lemma elems_insidence_one_zero:
  assumes "i < card (Vs E)"
  assumes "j < card E"
  shows "(insidence_mat E) $$ (i,j) = 0 \<or> (insidence_mat E) $$ (i,j) = 1" 
  unfolding insidence_mat_def 
  by (simp add: assms(1) assms(2))

lemma at_most_two_ones:
  assumes "graph_invar E"
  assumes "k < card E"
  shows "\<exists> i < (card (Vs E)). \<exists> j < card (Vs E). i \<noteq> j \<and> 
              (insidence_mat E) $$ (i, k) = 1 \<and> (insidence_mat E) $$ (j, k) = 1 \<and>
              (\<forall> t < card (Vs E). (t\<noteq>i \<and> t \<noteq> j) \<longrightarrow> B $$ (t,k) = 0)"
  oops

lemma at_most_two_ones2:
  assumes "graph_invar E"
  assumes "k < card E"
  shows "\<exists> i < (card (Vs E)). \<exists> j < card (Vs E). i \<noteq> j \<and> 
              col (insidence_mat E) k = unit_vec (card (Vs E)) i + unit_vec (card (Vs E)) j"
  oops

lemma at_most_two_ones2:
  assumes "graph_invar E"
  assumes "k < card E"
  assumes "i < (card (Vs E))"
  assumes "j < (card (Vs E))"
  assumes "i \<noteq> j"
  assumes " (insidence_mat E) $$ (i, k) = 1 \<and> (insidence_mat E) $$ (j, k) = 1"
  shows "(\<forall> t < card (Vs E). (t\<noteq>i \<and> t \<noteq> j) \<longrightarrow> (insidence_mat E) $$ (t,k) = 0)"
proof safe
  fix t
  assume asm: "t < card (Vs E)" "t \<noteq> i" "t \<noteq> j"
  show "(insidence_mat E) $$ (t,k) = 0"
  proof(rule ccontr)
    assume "(insidence_mat E) $$ (t, k) \<noteq> 0" 
    then have "(insidence_mat E) $$ (t, k) = 1" 
      using asm(1) assms(2) gram_schmidt_floor.elems_insidence_one_zero by blast
    then have 1: "(vertices_list E) ! t \<in> (edges_list E) ! k" 
      using asm(1) assms(2) gram_schmidt_floor.one_then_in_edge by blast
    have 2: "(vertices_list E) ! i \<in> (edges_list E) ! k" 
      using assms(2) assms(3) assms(6) gram_schmidt_floor.one_then_in_edge by blast
    have 3: "(vertices_list E) ! j \<in> (edges_list E) ! k" 
      using assms(2) assms(4) assms(6) gram_schmidt_floor.one_then_in_edge by blast
    have "card ((edges_list E) ! k) \<noteq> 2"
    proof(cases "infinite ((edges_list E) ! k)")
      case True
      then show ?thesis 
        by simp
    next
      case False
      have "{(vertices_list E) ! i, (vertices_list E) ! j, (vertices_list E) ! t} \<subseteq> 
            (edges_list E) ! k"
        by (simp add: 1 2 3)
      then show ?thesis
        using diff_verts 
        by (metis 1 2 3 asm assms(3-5) card_2_iff')
    qed
    have "(edges_list E) ! k \<in> E" using edges_list_el_in_E 
      using assms(2) by blast 
    then show False 
      using card_edge[of E] \<open>card (edges_list E ! k) \<noteq> 2\<close> assms(1) by fastforce
  qed
qed

lemma dim_row_mat_less_card_I:
  assumes "finite I" 
  shows "dim_row (submatrix A I J) \<le> card I" 
proof -
  have "{i. i < dim_row A \<and> i \<in> I} \<subseteq> I" by auto
  then have "card {i. i < dim_row A \<and> i \<in> I} \<le> card I" 
    using assms card_mono by blast
  then show ?thesis 
    by (simp add: dim_submatrix(1))
qed

lemma exist_index_in_submat:
  assumes "B = submatrix A I UNIV"
  assumes "j < dim_row B"
  shows "\<exists> i < dim_row A. i \<in> I \<and> row B j = row A i  \<and> i = pick I j"
proof -
  have "(pick I j) < dim_row A"  
    by (metis assms(1) assms(2) dim_submatrix(1) pick_le)
  moreover have "(pick I j) \<in> I" 
    apply(cases "finite I") 
    using  dim_row_mat_less_card_I pick_in_set_le 
     apply (metis assms(1) assms(2) order_trans_rules(22))
    using pick_in_set_inf by auto
  ultimately show ?thesis 
    by (metis (no_types, lifting) assms dim_submatrix(1) row_submatrix_UNIV)
qed

lemma submatrix_not_more_than_two:
  assumes "graph_invar E"
  assumes "k < dim_col B"
  assumes "i < dim_row B"
  assumes "j < dim_row B"
  assumes "i \<noteq> j"
  assumes "B = submatrix (insidence_mat E) I J"
  assumes "B $$ (i, k) = 1 \<and> B $$ (j, k) = 1"
  shows "(\<forall> t < dim_row B. (t\<noteq>i \<and> t \<noteq> j) \<longrightarrow> B $$ (t,k) = 0)"
proof safe
  fix t
  assume asm: "t < dim_row B" "t \<noteq> i" "t \<noteq> j"
  obtain i1 where i1: "row (insidence_mat E) i1 = 
        row (submatrix (insidence_mat E) I UNIV) i \<and>
        i1 < dim_row (insidence_mat E) \<and> 
        i1 = pick I i"
    using exist_index_in_submat 
    by (metis (no_types, lifting) assms(3,6) dim_submatrix(1) exist_index_in_submat) 
  obtain j1 where j1: "row (insidence_mat E) j1 = 
        row (submatrix (insidence_mat E) I UNIV) j \<and> 
        j1 < dim_row (insidence_mat E) \<and> 
        j1 = pick I j"
    using exist_index_in_submat 
    by (metis (no_types, lifting) assms(4,6) dim_submatrix(1) exist_index_in_submat) 
  obtain t1 where t1: "row (insidence_mat E) t1 = 
        row (submatrix (insidence_mat E) I UNIV) t \<and> 
        t1 < dim_row (insidence_mat E) \<and> 
        t1 = pick I t"
    using exist_index_in_submat 
    by (metis (no_types, lifting) asm(1) assms(6) dim_submatrix(1) exist_index_in_submat) 
  have "dim_col B = card {i. i < dim_col (insidence_mat E) \<and> i \<in> J}" 
    using assms(6) dim_submatrix(2) by blast
  then obtain k1 where k1: "col (insidence_mat E) k1 = 
         col (submatrix (insidence_mat E) UNIV J) k \<and>
         k1 < dim_col (insidence_mat E) \<and> 
         k1 = pick J k" 
    using pick_le col_submatrix_UNIV 
    by (metis (no_types, lifting) Collect_cong \<open>k < dim_col B\<close>)
  have "k1 < card E" 
    using dim_col_insidence_mat k1 by metis
  have "i1 < (card (Vs E))"
    using dim_row_insidence_mat i1 by metis
  have "j1 < (card (Vs E))" 
    using dim_row_insidence_mat j1 by metis
  have "pick I i \<noteq> pick I j" 
    by (metis assms(3-6) diff_is_0_eq diff_less_mono dim_row_mat_less_card_I less_irrefl not_less
        not_less_iff_gr_or_eq not_less_zero pick_mono_inf pick_mono_le)
  then have "i1 \<noteq> j1" 
    using i1 j1 by blast
  have "(insidence_mat E) $$ (pick I i, pick J k) = B  $$ (i,k)" 
    by (metis (no_types, lifting) assms(2,3,6) dim_submatrix(1-2) submatrix_index)
  then have "(insidence_mat E) $$ (i1, k1) = 1" 
    using assms(7) i1 k1 by presburger
  have "(insidence_mat E) $$ (pick I j, pick J k) = B  $$ (j,k)" 
    by (metis (no_types, lifting) assms(2,4,6) dim_submatrix(1-2) submatrix_index)
  then have "(insidence_mat E) $$ (j1, k1) = 1" 
    using assms(7) j1 k1 by presburger
  then have 1: "(\<forall> t < card (Vs E). (t\<noteq>i1 \<and> t \<noteq> j1) \<longrightarrow> (insidence_mat E) $$ (t,k1) = 0)"
    by (meson \<open>i1 < card (Vs E)\<close> \<open>i1 \<noteq> j1\<close> \<open>insidence_mat E $$ (i1, k1) = 1\<close> \<open>j1 < card (Vs E)\<close>
        \<open>k1 < card E\<close> assms(1) gram_schmidt_floor.at_most_two_ones2)
  have "pick I t \<noteq> pick I i"
    by (metis asm(1,2) assms(3,6) diff_is_0_eq diff_less_mono dim_row_mat_less_card_I less_irrefl
        not_less not_less_iff_gr_or_eq not_less_zero pick_mono_inf pick_mono_le)
  have "pick I t \<noteq> pick I j"
    by (metis asm(1,3) assms(4,6) diff_is_0_eq diff_less_mono dim_row_mat_less_card_I less_irrefl 
        not_less not_less_iff_gr_or_eq not_less_zero pick_mono_inf pick_mono_le)
  then have "(insidence_mat E) $$ (t1, k1) = 0" 
    by (metis 1 \<open>pick I t \<noteq> pick I i\<close> dim_row_insidence_mat i1 j1 t1)
  show "B $$ (t,k) = 0"
    by (metis (no_types, lifting) \<open>insidence_mat E $$ (t1, k1) = 0\<close> asm(1) assms(2,6) 
        dim_submatrix(1-2) k1 submatrix_index t1)
qed

lemma submatrix_insidence_zero_or_one:
  assumes "graph_invar E"
  assumes "k < dim_col B"
  assumes "i < dim_row B"
  assumes "B = submatrix (insidence_mat E) I J"
  shows "B $$ (i, k) = 1 \<or> B $$ (i, k) = 0"
proof -
  have 1: "B $$ (i, k) = (insidence_mat E) $$ (pick I i, pick J k)" 
    by (metis (no_types, lifting) assms(2-4) dim_submatrix(1-2) submatrix_index)
  have "pick I i < card (Vs E)" 
    by (metis (no_types, lifting) assms(3,4) dim_submatrix(1) exist_index_in_submat 
        gram_schmidt_floor.dim_row_insidence_mat)
  have "pick J k < card E" 
    by (metis assms(2,4) dim_col_insidence_mat dim_submatrix(2) pick_le)
  have "(insidence_mat E) $$ (pick I i, pick J k) = 1 \<or> 
        (insidence_mat E) $$ (pick I i, pick J k) = 0"
    using \<open>pick I i < card (Vs E)\<close> \<open>pick J k < card E\<close> elems_insidence_one_zero by blast
  then show ?thesis 
    using 1 by presburger
qed

lemma bipartite_submatrix_det_unimod:
  assumes "bipartite E" 
  assumes "B = submatrix (insidence_mat E) I J"
  shows "det B \<in> {-1, 0, 1}" using assms(2)
proof(induct "dim_row B" arbitrary: B I J rule: less_induct)
  case less
  show ?case
  proof(cases "dim_row B \<noteq> dim_col B")
    case True
    then show ?thesis 
      unfolding Determinant.det_def  
      by (meson insertCI)
  next
    case False
    have 1: "dim_row B = dim_col B" using False by auto
    then show ?thesis 
    proof(cases "carrier class_ring = {\<zero>\<^bsub>class_ring\<^esub> ::'a}")
      case True
      have "carrier class_ring = {\<zero>\<^bsub>class_ring\<^esub> ::'a}" 
        using True by fast
      then have "det B = 0" 
        by auto
      then show ?thesis 
        by blast
    next
      case False
      show ?thesis
      proof(cases "\<exists> j < dim_col B. col B j = 0\<^sub>v (dim_row B)")
        case True
        obtain j where " j < dim_col B \<and> col B j = 0\<^sub>v (dim_row B)" 
          using True by blast
        have 2:"B \<in> carrier_mat (dim_row B) (dim_row B)" 
          by (metis "1" carrier_matI)
        have "0\<^sub>v (dim_row B) \<in> (set (cols B))" 
          by (metis True cols_length cols_nth in_set_conv_nth)
        have 3:"\<zero>\<^bsub>module_vec TYPE('a) (dim_row B)\<^esub>\<in> set (cols B)" 
          by (metis \<open>0\<^sub>v (dim_row B) \<in> set (cols B)\<close> module_vec_simps(2))
        have 4:"Module.module class_ring (module_vec TYPE('a) (dim_row B))" 
          using vec_module by blast
        have 5:" carrier class_ring \<noteq> {\<zero>\<^bsub>class_ring\<^esub> ::'a}" using False
          by simp
        have "module.lin_dep class_ring
     (module_vec TYPE('a) (dim_row B))
     (set (cols B))" 
          using module.zero_lin_dep[OF 4 3 5]
          by fastforce
        then have "det B = 0" 
          using idom_vec.lin_dep_cols_imp_det_0[OF 2] 
          by blast
        then show ?thesis 
          by force
      next
        case False
        show ?thesis
        proof(cases "\<exists>j<dim_col B. \<exists> i < dim_row B. col B j = unit_vec (dim_row B) i")
          case True
          have 2:"B \<in> carrier_mat (dim_row B) (dim_row B)" 
            by (metis "1" carrier_matI)
          obtain j i where i_j:"j<dim_col B \<and> i < dim_row B \<and> col B j = unit_vec (dim_row B) i"
            using True by auto
          have 3: "j < dim_row B" using i_j 
            using "1" by presburger
          have 10: "det B = (\<Sum>k<dim_row B. B $$ (k,j) * cofactor B k j)"
            using laplace_expansion_column[OF 2 3] 
            by presburger
          have "\<forall>k<dim_row B. k \<noteq> i \<longrightarrow> B $$ (k,j) = 0" 
          proof safe
            fix k 
            assume asm: "k < dim_row B" "k\<noteq>i"
            have "B $$ (k,j) = col B j $ k" 
              by (metis asm(1) i_j index_col)
            have "unit_vec (dim_row B) i $ k = 0"
              unfolding unit_vec_def 
              by (simp add: i_j asm)
            show "B $$ (k, j) = 0" 
              by (metis \<open>B $$ (k, j) = col B j $v k\<close> \<open>unit_vec (dim_row B) i $v k = 0\<close> i_j)
          qed
          then have "(\<Sum>k \<in> {0..<dim_row B}. B $$ (k,j) * cofactor B k j) =
               B $$ (i,j) * cofactor B i j" 
            by (metis (mono_tags, lifting) atLeast0LessThan only_one_nonzero_is_sum 
                finite_atLeastLessThan i_j lessThan_iff vector_space_over_itself.scale_eq_0_iff)
          then have 13: "det B = B $$ (i,j) * cofactor B i j" 
            by (metis 10 atLeast0LessThan)
          have 8:"cofactor B i j = (-1)^(i+j) * det (mat_delete B i j)" 
            using Determinant.cofactor_def by blast
          have 9:"mat_delete B i j = submatrix (insidence_mat E) (I - {pick I i}) (J - {pick J j})"
            using mat_delete_is_submatrix i_j less(2) by blast
          have 11: "dim_row ( submatrix (insidence_mat E) (I - {pick I i}) (J - {pick J j})) < 
                    dim_row B" 
            by (metis "9" bot_nat_0.not_eq_extremum diff_less i_j less_nat_zero_code 
                less_one mat_delete_dim(1))
          have "det (submatrix (insidence_mat E) (I - {pick I i}) (J - {pick J j})) \<in> {-1, 0, 1}" 
            using 11 less(1) by presburger
          then have "det (mat_delete B i j) \<in> {-1, 0, 1}" 
            using "9" by presburger
          then have 12: "cofactor B i j \<in> {-1, 0, 1}" 
            by (smt (verit, ccfv_SIG) 8 insert_iff mult_cancel_right2 mult_minus1 nat_pow_distrib
                singletonD square_eq_1_iff vector_space_over_itself.scale_eq_0_iff)
          have "B $$ (i,j) = col B j $ i" 
            by (metis i_j index_col)
          have "unit_vec (dim_row B) i $ i = 1" 
            unfolding unit_vec_def 
            by (simp add: i_j)
          then have "B $$ (i,j) = 1" 
            by (simp add: \<open>B $$ (i, j) = col B j $v i\<close> i_j)
          then show ?thesis 
            by (metis 12 13 mult_cancel_right2)
        next
          case False
          show ?thesis
          proof(cases "dim_row B = 0")
            case True
            have "det B = 1" using det_dim_zero 
              by (metis "1" True carrier_mat_triv)
            then show ?thesis by auto
          next
            case False
            have 4:"dim_row B > 0" using False by auto
            have 5:"\<forall> k < dim_col B. \<exists> i < dim_row B. \<exists> j < dim_row B. 
                    B $$ (i, k) = 1 \<and> B $$ (j, k) = 1 \<and> i\<noteq>j" 
              apply safe
              apply (rule ccontr)
            proof -
              fix k
              assume "k < dim_col B"
              assume asm_not: "\<not> (\<exists>i<dim_row B. \<exists>j<dim_row B.
                               B $$ (i, k) = 1 \<and> B $$ (j, k) = 1 \<and> i \<noteq> j)"
              have "col B k \<noteq> 0\<^sub>v (dim_row B)"
                using `\<not> (\<exists>j<dim_col B. col B j = 0\<^sub>v (dim_row B))` 
                using \<open>k < dim_col B\<close> by blast
              have "\<exists> i < dim_row B. B $$ (i, k) = 1"
              proof(rule ccontr)
                assume "\<not> (\<exists>i<dim_row B. B $$ (i, k) = 1)"
                then have "\<forall>i<dim_row B. B $$ (i, k) = 0" 
                  by (metis \<open>k < dim_col B\<close> assms(1) bipartite_def 
                      gram_schmidt_floor.submatrix_insidence_zero_or_one less.prems)
                then have "\<forall>i<dim_row B. col B k $ i = 0"
                  by (metis \<open>k < dim_col B\<close> index_col)
                then have "col B k = 0\<^sub>v (dim_row B)"
                  unfolding zero_vec_def 
                  by (metis Matrix.zero_vec_def dim_col dim_vec eq_vecI index_zero_vec(1))
                then show False
                  using `col B k \<noteq> 0\<^sub>v (dim_row B)` by auto
              qed
              then obtain i where i: "i < dim_row B \<and> B $$ (i, k) = 1" by auto
              have 13: "\<forall> j < dim_row B. i \<noteq> j \<longrightarrow>  B $$ (j, k) = 0" 
              proof safe
                fix j
                assume asm: "j < dim_row B" "i \<noteq> j"
                show " B $$ (j, k) = 0"
                proof(rule ccontr)
                  assume "B $$ (j, k) \<noteq> 0"
                  then have "B $$ (j, k) = 1" 
                    using submatrix_insidence_zero_or_one 
                    by (metis \<open>k < dim_col B\<close> asm(1) assms(1) bipartite_def less.prems)
                  then show False 
                    using asm_not i asm(1) asm(2) by blast
                qed
              qed
              have "col B k = unit_vec (dim_row B) i" 
              proof 
                show 14: "dim_vec (col B k) = dim_vec (unit_vec (dim_row B) i)"
                  by (metis dim_col index_unit_vec(3))
                fix ia
                assume "ia < dim_vec (unit_vec (dim_row B) i)" 
                then show "col B k $v ia = unit_vec (dim_row B) i $v ia" 
                  by (metis 13 14 i \<open>k < dim_col B\<close> dim_col index_col index_unit_vec(1))
              qed
              then show False using `\<not> (\<exists>j<dim_col B. \<exists>i<dim_row B. col B j = unit_vec (dim_row B) i)`
                using \<open>i < dim_row B \<and> B $$ (i, k) = 1\<close> \<open>k < dim_col B\<close> by blast
            qed
            obtain X where X: "graph_invar E \<and> 
                               X \<subseteq> Vs E \<and> (\<forall> e \<in> E. \<exists> u v.  e = {u, v} \<and> (u \<in> X \<and> v \<in> Vs E - X))"
              using assms(1) unfolding bipartite_def by auto
            let ?u = "vec (dim_row B) 
                      (\<lambda> i. if (vertices_list E) ! pick I i \<in> X then (1::'a)  else -1)"
            define u where "u =?u" 
            have "\<forall> i < dim_row B. ?u $ i = 1 \<or> ?u $ i = -1" 
              by simp
            then have 32:"?u \<noteq> 0\<^sub>v (dim_row B)" 
              by (metis "4" class_field.neg_1_not_0 class_field.zero_not_one index_zero_vec(1))
            have "\<forall> t < dim_col B. col B t \<bullet> ?u = 0"
            proof safe
              fix t
              assume t: "t < dim_col B"
              obtain i j where i_j: "B $$ (i,t) = 1" 
                "B $$ (j, t) = 1"
                "i < dim_row B" 
                "j < dim_row B" "i \<noteq> j" 
                using 5 t by blast
              have 6:"graph_invar E" 
                by (meson X)
              have "\<forall>k < dim_row B. (k \<noteq> i \<and> k \<noteq> j) \<longrightarrow> B $$ (k,t) = 0" 
                using submatrix_not_more_than_two[OF 6 t i_j(3) i_j(4) i_j(5) less(2)] using  i_j 
                by blast 
              then have 15: "\<forall>k < dim_row B. (k \<noteq> i \<and> k \<noteq> j) \<longrightarrow> col B t $ k = 0" 
                by (metis index_col t)
              have 21: "col B t \<bullet> ?u = sum (\<lambda> k. (col B t $ k) * (?u $ k)) {0..<dim_row B}"
                unfolding scalar_prod_def 
                by (metis dim_vec)
              have 19: "sum (\<lambda> k. (col B t $ k) * (?u $ k)) {0..<dim_row B} = 
                        (col B t $ i) * (?u $ i) + (col B t $ j) * (?u $ j)" 
              proof -
                have 17: "sum (\<lambda> k. (col B t $ k) * (?u $ k)) {0..<dim_row B} = 
                      sum (\<lambda> k. (col B t $ k) * (?u $ k)) ({0..<dim_row B} - {i,j}) 
                       + sum (\<lambda> k. (col B t $ k) * (?u $ k)) {i,j}" 
                  by (meson atLeastLessThan_iff empty_subsetI finite_atLeastLessThan i_j(3) i_j(4) 
                      insert_subset sum.subset_diff zero_order(1))
                have 16: "\<forall> k \<in> ({0..<dim_row B} - {i,j}). (col B t $ k) * (?u $ k) = 0" 
                  by (metis Diff_iff 15 atLeastLessThan_iff insertCI 
                      vector_space_over_itself.scale_eq_0_iff)
                have 18: "sum (\<lambda> k. (col B t $ k) * (?u $ k)) ({0..<dim_row B} - {i,j}) = 0" 
                  by (metis (no_types, lifting) R.add.finprod_all1 16)
                have "sum (\<lambda> k. (col B t $ k) * (?u $ k)) {i,j} = 
                      (col B t $ i) * (?u $ i) + (col B t $ j) * (?u $ j)"
                  by (meson i_j(5) sum_two_elements)
                then show ?thesis 
                  using R.show_l_zero 17 18 by presburger
              qed
              have 20: "(col B t $ i) = 1 \<and> (col B t $ j) = 1" 
                by (metis i_j(1) i_j(2) i_j(3) i_j(4) index_col t)
              have 30: "col B t \<bullet> ?u = (?u $ i) + (?u $ j)" 
                using 19 20 21 cring_simprules(12) by presburger
              have "pick J t < card E" 
                by (metis dim_submatrix(2) gram_schmidt_floor.dim_col_insidence_mat 
                    less(2) pick_le t)
              have "insidence_mat E $$ (pick I i, pick J t) = 1" 
                by (metis (no_types, lifting) dim_submatrix(1) dim_submatrix(2) i_j(1) i_j(3) 
                    less(2) submatrix_index t)
              then have 23: "vertices_list E ! pick I i \<in> edges_list E! pick J t" 
                by (metis (no_types, lifting) \<open>pick J t < card E\<close> dim_submatrix(1) i_j(3) less(2)
                    exist_index_in_submat gram_schmidt_floor.dim_row_insidence_mat one_then_in_edge)
              have "insidence_mat E $$ (pick I j, pick J t) = 1"
                by (metis (no_types, lifting) dim_submatrix(1) dim_submatrix(2) i_j(2) i_j(4) 
                    less(2) submatrix_index t)
              then have 24: "vertices_list E ! pick I j \<in> edges_list E! pick J t" 
                by (metis (no_types, lifting) \<open>pick J t < card E\<close> dim_submatrix(1) 
                    exist_index_in_submat gram_schmidt_floor.dim_row_insidence_mat
                    gram_schmidt_floor.one_then_in_edge i_j(4) less(2))
              have 22: "(edges_list E! pick J t) \<in> E"
                using edges_list_el_in_E
                using \<open>pick J t < card E\<close> by blast
              have 27: "vertices_list E ! pick I i \<noteq> vertices_list E ! pick I j"             
                by (smt (verit, ccfv_SIG) diff_verts dim_row_mat_less_card_I dim_submatrix(1) 
                    exist_index_in_submat gram_schmidt_floor.dim_row_insidence_mat i_j(3-5)
                    le_neq_implies_less less(2) less_or_eq_imp_le not_less order_trans_rules(23)
                    pick_eq_iff_inf pick_mono_le)
              then have 25: "edges_list E! pick J t = 
                         {vertices_list E ! pick I i, vertices_list E ! pick I j}"
                using 6 22 23 24 by fastforce
              have 29: "(?u $ i) + (?u $ j) = 0"
              proof(cases "vertices_list E ! pick I i \<in> X")
                case True
                have 26: "(?u $ i) = 1" 
                  by (simp add: True i_j(3))
                have "vertices_list E ! pick I j \<notin> X" 
                  using True 25 22 X insert_absorb by fastforce
                then have "?u $ j = -1" 
                  by (simp add: i_j(4))
                then show ?thesis 
                  using 26 by linarith
              next
                case False
                have 28: "(?u $ i) = - 1" 
                  by (simp add: False i_j(3))
                have "vertices_list E ! pick I j \<in> X" 
                  using False 22 X 23 27 24 by force
                then have "?u $ j = 1" 
                  by (simp add: i_j(4))
                then show ?thesis 
                  using 28 by linarith
              qed
              show "col B t \<bullet> ?u = 0" 
                using 29 30 by presburger
            qed
            then have "\<forall> t < dim_row B\<^sup>T. row B\<^sup>T t \<bullet> ?u = 0" 
              by (metis Matrix.col_transpose Matrix.transpose_transpose index_transpose_mat(2))
            then have 31: "B\<^sup>T *\<^sub>v ?u = 0\<^sub>v (dim_row B\<^sup>T)" 
              unfolding mult_mat_vec_def zero_vec_def
              by (metis (no_types, lifting) dim_vec eq_vecI index_transpose_mat(2) index_vec) 
            have 3: "\<exists>v. v \<in> carrier_vec (dim_row B\<^sup>T) \<and> 
                        v \<noteq> 0\<^sub>v (dim_row B\<^sup>T) \<and> B\<^sup>T *\<^sub>v v = 0\<^sub>v (dim_row B\<^sup>T)" 
              by (metis "1" 31 32 index_transpose_mat(2) vec_carrier)
            have 2: "B\<^sup>T \<in> carrier_mat (dim_row B) (dim_row B)" using 1 
              by auto
            then have "det B\<^sup>T = 0" 
              using det_0_iff_vec_prod_zero[OF 2] using 3 1
              by (metis index_transpose_mat(2))
            then have "det B = 0" 
              by (metis "2" Determinant.det_transpose Matrix.transpose_transpose)
            then show ?thesis 
              by blast
          qed
        qed
      qed
    qed
  qed
qed

lemma bipartite_tot_unimod:
  assumes "bipartite E"
  shows "tot_unimodular (insidence_mat E)" 
proof -
  have "(\<forall> B. (\<exists> I J. submatrix (insidence_mat E) I J = B) \<longrightarrow> det B \<in> {-1, 0, 1})"
    by (meson assms bipartite_submatrix_det_unimod)
  then show ?thesis
    using tot_unimodular_def by blast
qed

lemma matching_polyh_int:
  assumes "bipartite E"
  shows "gram_schmidt_floor.int_polyh (card E) 
            (gram_schmidt_floor.pos_polyhedron (card E) (insidence_mat E) (1\<^sub>v (card (Vs E))))"
proof -
  have 4:"tot_unimodular (insidence_mat E)" 
    using bipartite_tot_unimod assms by auto
  have 1:"1\<^sub>v (card (Vs E)) \<in> \<int>\<^sub>v" 
    using gram_schmidt.one_vec_int by blast
  have 2:"(insidence_mat E) \<in> carrier_mat (card (Vs E)) (card E)" 
    using dim_col_insidence_mat dim_row_insidence_mat by blast
  then show "gram_schmidt_floor.int_polyh (card E) 
            (gram_schmidt_floor.pos_polyhedron (card E) (insidence_mat E) (1\<^sub>v (card (Vs E))))"
    using gram_schmidt_floor.tot_unimod_then_int_polyhedron[OF 2 4] 
    using "1" one_carrier_vec by blast
qed

end
end