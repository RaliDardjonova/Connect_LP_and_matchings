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

(*
lemma tot_unimod_entries:
  assumes "tot_unimodular A"
  shows "elements_mat A \<subseteq> {-1, 0, 1}"
  sorry
*)

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

lemma ovndsovn:
   assumes A: "A \<in> carrier_mat nr n" 
   shows "mat_delete A i j = submatrix A ({0..<nr} - {i}) ({0..<n} - {j})"
  oops

lemma fewfwef:
  assumes A: "A \<in> carrier_mat nr1 n" 
  assumes B: "A \<in> carrier_mat nr2 n" 
  assumes "submatrix (A @\<^sub>r B) I J = C"
  assumes "I \<inter> {nr1..<nr1+nr2} = {}"
  shows "submatrix A I J = C"
  oops

lemma onwveov:
 assumes A: "A \<in> carrier_mat nr n" 
 assumes "nr - 1 \<in> I"
 shows "row (submatrix A I UNIV) (dim_row (submatrix A I UNIV) - 1) = row A (nr-1)"
proof(cases "nr=0")
  case True
  then show ?thesis 
    by (metis (no_types, lifting) Collect_empty_eq assms(1) carrier_matD(1) 
        class_semiring.add.one_closed dim_col_submatrix_UNIV dim_submatrix(1) eq_matI 
        less_nat_zero_code pick_UNIV pick_card_in_set)
next
  case False
  have "{i. i < dim_row A \<and> i \<in> I} \<noteq> {}" 
    using A False assms(2) by force
  have "card {i. i < dim_row A \<and> i \<in> I} > 0" 
    using \<open>{i. i < dim_row A \<and> i \<in> I} \<noteq> {}\<close> card_gt_0_iff finite_nat_set_iff_bounded by blast
  let ?i = "dim_row (submatrix A I UNIV) - 1"
  have 1: "?i < card {i. i < dim_row A \<and> i \<in> I}" 
    using dim_submatrix(1)[of A I UNIV] 
    using \<open>0 < card {i. i < dim_row A \<and> i \<in> I}\<close> by linarith
  have "row (submatrix A I UNIV) ?i = row A (pick I ?i)"
    using row_submatrix_UNIV 
    using \<open>?i < card {i. i < dim_row A \<and> i \<in> I}\<close> by blast
  have "pick I ?i < dim_row A"
    using pick_le[of ?i "dim_row A" I] 1 
    by fast
  then have "pick I ?i \<le> nr - 1" 
    using A le_diff_iff' le_less_linear by auto
  have "card {i. i < dim_row A \<and> i \<in> I} = dim_row (submatrix A I UNIV)" 
    by (simp add: dim_submatrix(1))
  have "{i. i < dim_row A \<and> i \<in> I} = {a \<in> I. a < nr - 1} \<union> {nr-1}" 
    apply safe
    using A apply auto[1]
    using A apply auto[1]
    using A False diff_less less_numeral_extra(1) apply blast
    using assms(2) by fastforce
  then have "card {i. i < dim_row A \<and> i \<in> I} - 1 = card {a \<in> I. a < nr - 1}" 
    by force
  then have "card {a \<in> I. a < nr - 1} = ?i" 
    using \<open>card {i. i < dim_row A \<and> i \<in> I} = dim_row (submatrix A I UNIV)\<close> by presburger
  then have "pick I ?i = nr - 1" 
    by (metis assms(2) pick_card_in_set)
  then show ?thesis 
    using \<open>Matrix.row (submatrix A I UNIV) (dim_row (submatrix A I UNIV) - 1) = Matrix.row A (pick I (dim_row (submatrix A I UNIV) - 1))\<close> by presburger
qed



lemma fwfqwfpppjnb:
  assumes "card {i. i < k \<and> i \<in> I} < card I \<or> infinite I"
  shows "pick I (card {i. i < k \<and> i \<in> I}) \<ge> k"
proof -
  have "pick I (card {a \<in> I. a < k}) = (LEAST a. a \<in> I \<and> k \<le> a)"
    using pick_card by blast
  have "pick I (card {a \<in> I. a < k}) \<in> I" 
    by (metis (no_types, lifting) Collect_cong assms pick_in_set_inf pick_in_set_le)
  have "(LEAST a. a \<in> I \<and> k \<le> a) \<in> I" 
    using \<open>pick I (card {a \<in> I. a < k}) = (LEAST a. a \<in> I \<and> k \<le> a)\<close> \<open>pick I (card {a \<in> I. a < k}) \<in> I\<close> by presburger
  have "(LEAST a. a \<in> I \<and> k \<le> a) \<ge> k"
  proof (rule ccontr)
    assume "\<not> k \<le> (LEAST a. a \<in> I \<and> k \<le> a)"
    then  have " k > (LEAST a. a \<in> I \<and> k \<le> a)" 
      by linarith
    have "\<exists> t. t \<in> I \<and> t \<ge> k"
    proof(rule ccontr)
      assume "\<nexists>t. t \<in> I \<and> k \<le> t"
      then have "finite I" 
        by (meson infinite_nat_iff_unbounded_le)
      have "card {i. i < k \<and> i \<in> I} < card I"
        using \<open>finite I\<close> assms by blast
      have "card {a\<in>I. a < pick I (card {i. i < k \<and> i \<in> I})} = card {i. i < k \<and> i \<in> I}"
        using \<open>card {i. i < k \<and> i \<in> I} < card I\<close> card_pick by blast
      then show False 
        by (metis (mono_tags, lifting) Collect_cong Collect_mem_eq \<open>\<nexists>t. t \<in> I \<and> k \<le> t\<close> \<open>card {i. i < k \<and> i \<in> I} < card I\<close> not_less order.refl)
    qed
   
    then obtain t where "t \<in> I \<and> t \<ge> k" by auto
    then show False using LeastI[of "\<lambda> a. a \<in> I \<and> k \<le> a" t] 
      using \<open>\<not> k \<le> (LEAST a. a \<in> I \<and> k \<le> a)\<close> by presburger
  qed
  then show ?thesis
    by (simp add: \<open>pick I (card {a \<in> I. a < k}) = (LEAST a. a \<in> I \<and> k \<le> a)\<close> set_le_in)
qed


lemma pick_suc_diff_set:
  assumes "Suc j < card J \<or> infinite J"
  shows "pick J (Suc j) = pick (J - {pick J j}) j" 
proof(cases "infinite J")
  case True
  have "pick J (Suc j) > pick J j" 
    using True pick_mono_le 
    using lessI pick_mono by presburger
  have "pick J (Suc j) \<in> J - {pick J j}" 
    by (metis Diff_iff True \<open>pick J j < pick J (Suc j)\<close> nat_neq_iff pick_in_set_inf singletonD)
 then have 1: "pick (J - {pick J j}) (card {a\<in>(J - {pick J j}). a < pick J (Suc j)}) = pick J (Suc j)"
    using pick_card_in_set 
    by presburger
  have "{a\<in>(J - {pick J j}). a < pick J (Suc j)} \<union> {pick J j} = {a\<in>J. a < pick J (Suc j)}"
    apply safe 
     apply (simp add: True pick_in_set)
    using \<open>pick J j < pick J (Suc j)\<close> by blast
have "pick J j \<notin> {a\<in>(J - {pick J j}). a < pick J (Suc j)}"
    by blast
  have "card {a\<in>J. a < pick J (Suc j)} = (Suc j)" 
    using True card_pick by blast
  have "card ({a\<in>(J - {pick J j}). a < pick J (Suc j)} \<union> {pick J j}) = card {a\<in>(J - {pick J j}). a < pick J (Suc j)} + card {pick J j}"
    by force
  then have "card {a\<in>(J - {pick J j}). a < pick J (Suc j)} + 1 = card {a\<in>J. a < pick J (Suc j)}"
    by (metis \<open>{a \<in> J - {pick J j}. a < pick J (Suc j)} \<union> {pick J j} = {a \<in> J. a < pick J (Suc j)}\<close> card_eq_1_iff)
  then have "card {a\<in>(J - {pick J j}). a < pick J (Suc j)} = (Suc j) - 1" 
    using \<open>card {a \<in> J. a < pick J (Suc j)} = (Suc j)\<close> by presburger
  then have "pick (J - {pick J j}) ((Suc j) - 1) = pick J (Suc j)" using 1 
    by presburger
  then show ?thesis 
    by (metis diff_Suc_1)
next
  case False
  have "Suc j < card J" 
    using False assms by force
  have "pick J (Suc j) > pick J j" 
    using \<open>Suc j < card J\<close> pick_mono_le by blast
  have "pick J (Suc j) \<in> J - {pick J j}" 
    by (metis Diff_iff False \<open>pick J j < pick J (Suc j)\<close> assms nat_neq_iff pick_in_set_le singletonD)
  then have 1: "pick (J - {pick J j}) (card {a\<in>(J - {pick J j}). a < pick J (Suc j)}) = pick J (Suc j)"
    using pick_card_in_set 
    by presburger
  have "{a\<in>(J - {pick J j}). a < pick J (Suc j)} \<union> {pick J j} = {a\<in>J. a < pick J (Suc j)}"
    apply safe
     apply (simp add: Suc_lessD \<open>Suc j < card J\<close> pick_in_set_le)
    using \<open>pick J j < pick J (Suc j)\<close> by blast
  have "pick J j \<notin> {a\<in>(J - {pick J j}). a < pick J (Suc j)}"
    by blast
  have "card {a\<in>J. a < pick J (Suc j)} = (Suc j)" 
    using \<open>Suc j < card J\<close> card_pick by presburger
  have "card ({a\<in>(J - {pick J j}). a < pick J (Suc j)} \<union> {pick J j}) = card {a\<in>(J - {pick J j}). a < pick J (Suc j)} + card {pick J j}"
    by force
  then have "card {a\<in>(J - {pick J j}). a < pick J (Suc j)} + 1 = card {a\<in>J. a < pick J (Suc j)}"
    by (metis \<open>{a \<in> J - {pick J j}. a < pick J (Suc j)} \<union> {pick J j} = {a \<in> J. a < pick J (Suc j)}\<close> card_eq_1_iff)
  then have "card {a\<in>(J - {pick J j}). a < pick J (Suc j)} = (Suc j) - 1" 
    using \<open>card {a \<in> J. a < pick J (Suc j)} = (Suc j)\<close> by presburger
  then have "pick (J - {pick J j}) ((Suc j) - 1) = pick J (Suc j)" using 1 
    by presburger
  then show ?thesis 
    by (metis diff_Suc_1)
qed

lemma pipppi:
  assumes "j < card J \<or> infinite J"
  assumes "k < j"
  shows "pick (J - {pick J j}) k = pick J k"
proof -
  have 1: "k < card J \<or> infinite J" using assms by auto
  have "pick J (insert_index j k) = pick J k" unfolding insert_index_def 
    using assms(2) 
    by simp
  have "pick J k < pick J j" 
    using pick_mono
    using assms(2) assms(1) by blast    
  then have "pick J k \<in> J - {pick J j}" using pick_in_set[OF assms(1)]
    by (metis Diff_iff 1 nat_neq_iff pick_in_set singletonD)
  then have "pick (J - {pick J j}) (card {a\<in>(J - {pick J j}). a < pick J k}) = pick J k" 
    using pick_card_in_set 
    by presburger
  have "card {a\<in>J. a < pick J k} = k" 
    using 1 card_pick by blast
  have "pick J k < pick J j" 
    using \<open>pick J k < pick J j\<close> by blast
  then  have "{a\<in>J. a < pick J k} = {a\<in>(J - {pick J j}). a < pick J k}"
    by auto
  then show "pick (J - {pick J j}) k = pick J k" 
    using \<open>card {a \<in> J. a < pick J k} = k\<close> \<open>pick (J - {pick J j}) (card {a \<in> J - {pick J j}. a < pick J k}) = pick J k\<close> by presburger
qed



lemma pokkds:
  assumes "k < card J \<or> infinite J"
  assumes "j < k"
  shows "pick (J - {pick J j}) k = pick J (Suc k)"
proof -
  have "pick J k > pick J j" 
    using assms(1) assms(2) pick_mono by blast

  have "pick J k \<in> J - {pick J j}" 
    by (metis Diff_iff \<open>pick J j < pick J k\<close> assms(1) nat_neq_iff pick_in_set singletonD)
  then have 1: "pick (J - {pick J j}) (card {a\<in>(J - {pick J j}). a < pick J k}) = pick J k"
    using pick_card_in_set 
    by presburger
  have "{a\<in>(J - {pick J j}). a < pick J k} \<union> {pick J j} = {a\<in>J. a < pick J k}"
    apply safe
    using assms(1) assms(2) basic_trans_rules(19) pick_in_set apply blast
    by (simp add: \<open>pick J j < pick J k\<close>)
  have "pick J j \<notin> {a\<in>(J - {pick J j}). a < pick J k}"
    by blast
  have "card {a\<in>J. a < pick J k} = k" 
    using assms(1) card_pick by blast
  have "card ({a\<in>(J - {pick J j}). a < pick J k} \<union> {pick J j}) = card {a\<in>(J - {pick J j}). a < pick J k} + card {pick J j}"
    by force
  then have "card {a\<in>(J - {pick J j}). a < pick J k} + 1 = card {a\<in>J. a < pick J k}"
    by (metis \<open>{a \<in> J - {pick J j}. a < pick J k} \<union> {pick J j} = {a \<in> J. a < pick J k}\<close> card_eq_1_iff)
  then have "card {a\<in>(J - {pick J j}). a < pick J k} = k - 1" 
    using \<open>card {a \<in> J. a < pick J k} = k\<close> by presburger
  then have "pick (J - {pick J j}) (k - 1) = pick J k" using 1 
    by presburger
  have "pick (J - {pick J j}) (Suc (k - 1)) = (LEAST a. a \<in> (J - {pick J j}) \<and> pick (J - {pick J j}) (k - 1) < a)" 
    using DL_Missing_Sublist.pick.simps(2) by blast
  have "pick J (Suc k) = (LEAST a. a \<in> J \<and> pick J k < a)"
    using DL_Missing_Sublist.pick.simps(2) by blast
  have "(LEAST a. a \<in> (J - {pick J j}) \<and> pick (J - {pick J j}) (k - 1) < a) = 
              (LEAST a. a \<in> J \<and> pick J k < a)" 
    by (metis Diff_iff \<open>pick (J - {pick J j}) (k - 1) = pick J k\<close> \<open>pick J j < pick J k\<close> basic_trans_rules(19) less_not_refl2 singletonD)
  then show "pick (J - {pick J j}) k = pick J (Suc k)" 
    by (metis Suc_eq_plus1 \<open>card {a \<in> J - {pick J j}. a < pick J k} + 1 = card {a \<in> J. a < pick J k}\<close> \<open>card {a \<in> J - {pick J j}. a < pick J k} = k - 1\<close> \<open>card {a \<in> J. a < pick J k} = k\<close> \<open>pick (J - {pick J j}) (Suc (k - 1)) = (LEAST a. a \<in> J - {pick J j} \<and> pick (J - {pick J j}) (k - 1) < a)\<close> \<open>pick J (Suc k) = (LEAST a. a \<in> J \<and> pick J k < a)\<close>)
qed  

lemma fbfewlon:
assumes "Suc i < card I \<or> infinite I"
assumes "card {i. i < k \<and> i \<in> I} \<le> i" 
assumes "k \<in> I"
shows "pick (I - {k}) i  = pick I (Suc i)"
proof - 
  let ?j = "(card {a \<in> I. a < k})"
  have "pick I ?j = k" using pick_card_in_set 
    using assms(3) by presburger
  have "{a \<in> I. a < k} \<union> {k} = {i. i < Suc k \<and> i \<in> I}" 
    apply safe 
      apply linarith
    using assms(3) less_SucE by blast+
  then have "{a \<in> I. a < k} \<subset> {i. i < Suc k \<and> i \<in> I}" 
    by force
  then have "?j < card {i. i < Suc k \<and> i \<in> I}" 
    by (simp add: psubset_card_mono)
  then have "?j \<le> i" 
    using assms(2) basic_trans_rules(22) 
    by (smt (verit, best) Collect_cong)
  then show ?thesis 
  proof(cases "?j = i")
    case True
    have "pick I (Suc i) = pick (I - {pick I i}) i" 
      using pick_suc_diff_set[OF assms(1)] by auto
    then show ?thesis 
      by (metis (no_types, lifting) Suc_lessD \<open>card {a \<in> I. a < k} \<le> i\<close> \<open>pick I (card {a \<in> I. a < k}) = k\<close> assms(1) le_neq_implies_less pokkds)
  next
    case False
    then show ?thesis 
    using pokkds[of i I ?j] False 
    by (metis Suc_lessD \<open>card {a \<in> I. a < k} \<le> i\<close> \<open>pick I (card {a \<in> I. a < k}) = k\<close> assms(1) le_neq_implies_less pokkds)
qed
qed

lemma fbowejbowf:
assumes "i  < card I \<or> infinite I"
 assumes "card {i. i < Suc k \<and> i \<in> I} \<le> i" 
  shows "pick ((I - {i. i < Suc k \<and> i \<in> I})) ((i - card {i. i < Suc k \<and> i \<in> I})) =
    pick (I - {i. i < k \<and> i \<in> I}) (i - card {i. i < k \<and> i \<in> I})"
proof(cases "k \<in> I")
  case True
  let ?i = "i - card {i. i < Suc k \<and> i \<in> I}"
    let ?j = "(card {a \<in> I. a < k})"
  have "pick I ?j = k" using pick_card_in_set 
    using True by presburger
  have "{a \<in> I. a < k} \<union> {k} = {i. i < Suc k \<and> i \<in> I}" 
    apply safe 
      apply linarith
    using True less_SucE by blast+
  then have "{a \<in> I. a < k} \<subset> {i. i < Suc k \<and> i \<in> I}" 
    by force
  then have 3:"?j < card {i. i < Suc k \<and> i \<in> I}" 
    by (simp add: psubset_card_mono)
  then have "?j < i" 
    using assms(2) basic_trans_rules(22) by blast
  have "I - {i. i < Suc k \<and> i \<in> I} = (I - {i. i < k \<and> i \<in> I}) - {k}"
    by force
  have 2: "k \<in> I - {i. i < k \<and> i \<in> I}" 
    using True by force

  have 1: "Suc ?i < card (I - {i. i < k \<and> i \<in> I}) \<or> infinite (I - {i. i < k \<and> i \<in> I})" 
  proof(cases "infinite I")
    case True
    have "infinite (I - {i. i < k \<and> i \<in> I})" using True by auto
    then show ?thesis by auto
  next
    case False
    have "i < card I" 
      using False assms(1) by blast
    then have "?i < card I - card {i. i < Suc k \<and> i \<in> I}" 
      using assms(2) diff_less_mono by blast
    have "{i. i < k \<and> i \<in> I} \<subseteq> I" by auto
    then have "card (I - {i. i < k \<and> i \<in> I}) = card I - card {i. i < k \<and> i \<in> I}"
      by (simp add: card_Diff_subset)
    have "Suc ?i < card I - card {i. i < Suc k \<and> i \<in> I} + 1" 
      by (simp add: \<open>i - card {i. i < Suc k \<and> i \<in> I} < card I - card {i. i < Suc k \<and> i \<in> I}\<close>)
    then have "Suc ?i < card I - card {i. i < k \<and> i \<in> I}" 
      by (smt (verit, del_insts) "2" "3" Diff_iff False \<open>I - {i. i < Suc k \<and> i \<in> I} = I - {i. i < k \<and> i \<in> I} - {k}\<close> \<open>card (I - {i. i < k \<and> i \<in> I}) = card I - card {i. i < k \<and> i \<in> I}\<close> \<open>{i. i < k \<and> i \<in> I} \<subseteq> I\<close> basic_trans_rules(22) bot_least card.empty card.infinite card_Diff_insert card_Diff_subset card_mono card_seteq diff_card_le_card_Diff empty_iff finite.intros(1) less_Suc_eq_le less_diff_conv2 linorder_not_le minus_nat.simps(1) plus_1_eq_Suc)
  then show ?thesis 
      using \<open>card (I - {i. i < k \<and> i \<in> I}) = card I - card {i. i < k \<and> i \<in> I}\<close> by presburger
  qed

  have 3: "card {i. i < k \<and> i \<in> I - {i. i < k \<and> i \<in> I}}
            \<le> i - card {i. i < Suc k \<and> i \<in> I}" 
    by (metis (no_types, lifting) Collect_empty_eq DiffE card_eq_0_iff mem_Collect_eq zero_le)


  have 5:" pick (I - {i. i < k \<and> i \<in> I} - {k}) (i - card {i. i < Suc k \<and> i \<in> I}) =
  pick (I - {i. i < k \<and> i \<in> I}) (Suc (i - card {i. i < Suc k \<and> i \<in> I}))"
    using fbfewlon[OF 1 3 2] 
    by blast
  have "card {i. i < Suc k \<and> i \<in> I} = card ({i. i < k \<and> i \<in> I} \<union> {k})" 
    by (metis (no_types, lifting) Collect_cong \<open>{a \<in> I. a < k} \<union> {k} = {i. i < Suc k \<and> i \<in> I}\<close>)
  have "card {i. i < Suc k \<and> i \<in> I} =  card {i. i < k \<and> i \<in> I} + card {k}" 
    using \<open>card {i. i < Suc k \<and> i \<in> I} = card ({i. i < k \<and> i \<in> I} \<union> {k})\<close> by force
  then have "card {i. i < Suc k \<and> i \<in> I} = card {i. i < k \<and> i \<in> I} + 1" by auto
  then have 4: " (Suc (i - card {i. i < Suc k \<and> i \<in> I})) = (i - card {i. i < k \<and> i \<in> I})" 
    using assms(2) by linarith
  have "pick (I - {i. i < k \<and> i \<in> I} - {k}) (i - card {i. i < Suc k \<and> i \<in> I}) =
    pick ((I - {i. i < Suc k \<and> i \<in> I})) ((i - card {i. i < Suc k \<and> i \<in> I}))" 
    using \<open>I - {i. i < Suc k \<and> i \<in> I} = I - {i. i < k \<and> i \<in> I} - {k}\<close> by presburger
  then show ?thesis using 4 5 
    by presburger
next
  case False
  have "{i. i < Suc k \<and> i \<in> I} = {i. i <  k \<and> i \<in> I} \<union> {i. i=k \<and> i \<in> I}" 
    apply (simp only: less_Suc_eq)
    by blast
  then have "{i. i < Suc k \<and> i \<in> I} = {i. i <  k \<and> i \<in> I}" using False 
    by blast
  then show ?thesis 
    by presburger
qed



lemma ppknb:
assumes "i < card I \<or> infinite I"
  assumes "card {i. i < nr1 \<and> i \<in> I} \<le> i" 
  shows "pick (I - {i. i < nr1 \<and> i \<in> I}) (i - card {i. i < nr1 \<and> i \<in> I}) = 
      pick I i" using assms
proof(induct nr1)
  case 0
  then show ?case 
    by simp
next
  case (Suc nr1)
  have "card {i. i < nr1 \<and> i \<in> I} < card I \<or> infinite I"
  proof(cases "infinite I")
    case True
    then show ?thesis 
      by blast
  next
    case False
    have "{i. i < nr1 \<and> i \<in> I} \<subseteq>  {i. i < Suc nr1 \<and> i \<in> I}" by auto 
    then have "card {i. i < nr1 \<and> i \<in> I} \<le> card {i. i < Suc nr1 \<and> i \<in> I}"
      using False 
      by (simp add: card_mono)
    then show ?thesis 
      using Suc(2) Suc(3) by linarith
  qed
  have "finite {i. i < nr1 \<and> i \<in> I}" 
    by simp
  have "{i. i < nr1 \<and> i \<in> I} \<subseteq>  {i. i < Suc nr1 \<and> i \<in> I}" by auto 
  then have "card {i. i < nr1 \<and> i \<in> I} \<le> card {i. i < Suc nr1 \<and> i \<in> I}"
    by (simp add: card_mono)
  then have "card {i. i < nr1 \<and> i \<in> I} \<le> i" 
    using Suc(3) basic_trans_rules(23) by blast
  have " pick (I - {i. i < nr1 \<and> i \<in> I}) (i - card {i. i < nr1 \<and> i \<in> I}) =
    pick I i" 
    using Suc(1) \<open>card {i. i < nr1 \<and> i \<in> I} < card I \<or> infinite I\<close> \<open>card {i. i < nr1 \<and> i \<in> I} \<le> i\<close> 
    using Suc(2) by blast
  have " pick (I - {i. i < nr1 \<and> i \<in> I}) (i - card {i. i < nr1 \<and> i \<in> I}) =
       pick (I - {i. i < Suc nr1 \<and> i \<in> I}) (i - card {i. i < Suc nr1 \<and> i \<in> I})" 
    using fbowejbowf[of i I nr1] assms(1) 
    using Suc(3) by presburger  
  then show ?case 
    using \<open>pick (I - {i. i < nr1 \<and> i \<in> I}) (i - card {i. i < nr1 \<and> i \<in> I}) = pick I i\<close> by presburger
qed

lemma pfhwfipwqf:
  fixes I :: "nat set"
  assumes "i < card I \<or> infinite I"
  assumes "\<forall> i \<in> I. i \<ge> k"
 shows "pick ((\<lambda>i. i - k) ` I) i = pick I i - k"
proof(cases "I = {}")
  case True
  then show ?thesis 
    using assms by auto
next
  case False
 
  let ?f = "(\<lambda>i. i - k)"
  have "mono ?f" 
    by (simp add: diff_le_mono mono_def)
  have "\<exists>x\<in>I. \<forall>y\<in>I. x \<le> y" 
    by (metis Collect_mem_eq False empty_Collect_eq exists_least_iff le_simps(2) not_less_eq)
  then have "(LEAST a. a\<in>I) - k = (LEAST a. a\<in>(\<lambda>i. i - k) ` I)"
    by (simp add: Least_mono \<open>incseq (\<lambda>i. i - k)\<close>)

  show ?thesis using assms(1)
  proof(induct i)
    case 0
    have "pick ((\<lambda>i. i - k) ` I) 0 = (LEAST a. a\<in>(\<lambda>i. i - k) ` I)" 
      using DL_Missing_Sublist.pick.simps(1) 0 by blast
    have "pick I 0 - k = (LEAST a. a\<in>I) - k"
      using DL_Missing_Sublist.pick.simps(1) 0 
      by presburger
    then show ?case 
      using \<open>(LEAST a. a \<in> I) - k = (LEAST a. a \<in> (\<lambda>i. i - k) ` I)\<close> \<open>pick ((\<lambda>i. i - k) ` I) 0 = (LEAST a. a \<in> (\<lambda>i. i - k) ` I)\<close> by presburger
  next
    case (Suc i)
    have "i < card I \<or> infinite I" 
      using Suc(2) Suc_lessD by blast
    have "pick I i < pick I (Suc i)" 
      using Suc(2) lessI pick_mono_inf pick_mono_le by presburger
   
  


    have 1: "pick ((\<lambda>i. i - k) ` I) i = pick I i - k" 
      using Suc(1) \<open>i < card I \<or> infinite I\<close>  by blast
    have "pick ((\<lambda>i. i - k) ` I) (Suc i) = (LEAST a. a\<in>((\<lambda>i. i - k) ` I) \<and> a > pick ((\<lambda>i. i - k) ` I) i)"
      using DL_Missing_Sublist.pick.simps(2) by presburger
    then have "pick ((\<lambda>i. i - k) ` I) (Suc i) = (LEAST a. a\<in>((\<lambda>i. i - k) ` I) \<and> a > pick I i - k)"
      using "1" by presburger
    have "{a. a\<in>((\<lambda>i. i - k) ` I) \<and> a > pick I i - k} =
    (\<lambda>i. i - k) ` ( {x. x \<in> I \<and> x > pick I i})" 
      apply safe
        apply force+
      using 1 assms(2) 
      using \<open>i < card I \<or> infinite I\<close> diff_less_mono pick_in_set by presburger

    have "(LEAST a. a\<in>((\<lambda>i. i - k) ` I) \<and> a > pick I i - k) = 
        (LEAST a. a\<in>((\<lambda>i. i - k) ` ( {x. x \<in> I \<and> x > pick I i})))"
      by (metis (no_types, lifting) \<open>{a \<in> (\<lambda>i. i - k) ` I. pick I i - k < a} = (\<lambda>i. i - k) ` {x \<in> I. pick I i < x}\<close> mem_Collect_eq)
    have "pick I (Suc i) = (LEAST a. a\<in>I \<and> a > pick I i)"
      using DL_Missing_Sublist.pick.simps(2)
      by presburger
    have "(LEAST a. a\<in>I \<and> a > pick I i) = (LEAST a. a\<in> {x. x \<in> I \<and> x > pick I i})"
      by fastforce
    show ?case
    proof(cases "{x. x \<in> I \<and> x > pick I i} = {}")
      case True
      then show ?thesis 
        by (metis Suc.prems diff_Suc_1 diff_less_Suc empty_Collect_eq lessI pick_in_set pick_mono)
    next
      case False
 have 2: "\<exists>x\<in>{x. x \<in> I \<and> x > pick I i}. \<forall>y\<in>{x. x \<in> I \<and> x > pick I i}. x \<le> y" 
   using  Collect_mem_eq False empty_Collect_eq exists_least_iff le_simps(2) not_less_eq
   by (metis (no_types, lifting))

  have " (LEAST a. a\<in> {x. x \<in> I \<and> x > pick I i}) - k = 
      (LEAST a. a\<in>((\<lambda>i. i - k) ` ( {x. x \<in> I \<and> x > pick I i})))"
    using Least_mono[OF \<open>incseq (\<lambda>i. i - k)\<close> 2]  by auto

      then show ?thesis 
        using \<open>(LEAST a. a \<in> (\<lambda>i. i - k) ` I \<and> pick I i - k < a) = (LEAST a. a \<in> (\<lambda>i. i - k) ` {x \<in> I. pick I i < x})\<close> \<open>(LEAST a. a \<in> I \<and> pick I i < a) = (LEAST a. a \<in> {x \<in> I. pick I i < x})\<close> \<open>pick ((\<lambda>i. i - k) ` I) (Suc i) = (LEAST a. a \<in> (\<lambda>i. i - k) ` I \<and> pick I i - k < a)\<close> \<open>pick I (Suc i) = (LEAST a. a \<in> I \<and> pick I i < a)\<close> by presburger
    qed 
  qed
qed


lemma vwevwev:
  assumes "i < card I \<or> infinite I"
  assumes "card {i. i < k \<and> i \<in> I} \<le> i" 
  shows "pick ((\<lambda>i. i - k) ` (I - {0..<k})) (i - card {i. i < k \<and> i \<in> I}) =
        pick I i - k"
proof -
  have "(I - {0..<k}) = I - {i. i < k \<and> i \<in> I}"
    apply safe
     apply simp
    using atLeastLessThan_iff by blast

  have "pick (I - {i. i < k \<and> i \<in> I}) (i - card {i. i < k \<and> i \<in> I}) = 
      pick I i" 
    using assms(1) assms(2) ppknb by blast
  have 1: "\<forall> i \<in> I - {i. i < k \<and> i \<in> I}. i \<ge> k" 
    using linorder_not_less by blast
  have 2: "i -card {i. i < k \<and> i \<in> I} < card (I - {i. i < k \<and> i \<in> I}) \<or> 
      infinite (I - {i. i < k \<and> i \<in> I})" 
  proof(cases "infinite I")
    case True
    have " infinite (I - {i. i < k \<and> i \<in> I})" using True by auto
    then show ?thesis by auto
  next
    case False
    have "i < card I" using assms(1) False by auto
    have "card (I - {i. i < k \<and> i \<in> I}) = card I - card{i. i < k \<and> i \<in> I}" 
      by (metis (no_types, lifting) False card_Diff_subset finite_subset mem_Collect_eq subsetI)
    then show ?thesis 
      using False assms(1) assms(2) diff_less_mono by presburger
  qed

  have "pick ((\<lambda>i. i - k) ` (I - {i. i < k \<and> i \<in> I})) (i - card {i. i < k \<and> i \<in> I}) = 
        pick (I - {i. i < k \<and> i \<in> I}) (i - card {i. i < k \<and> i \<in> I}) - k"
      using pfhwfipwqf[OF 2 1]  
      by blast
    then show ?thesis 
      using \<open>I - {0..<k} = I - {i. i < k \<and> i \<in> I}\<close> \<open>pick (I - {i. i < k \<and> i \<in> I}) (i - card {i. i < k \<and> i \<in> I}) = pick I i\<close> by presburger
  qed


lemma bowqbfq:
  fixes I :: "nat set"
  shows "card {i. i < a \<and> i \<in> ((\<lambda> i. i - b) ` (I - {0..<b}))} = 
         card {i. i \<ge> b \<and> i < b + a \<and> i \<in> I}" 
proof(induct a rule:nat_induct)
  case 0

  then show ?case by simp
next
  case (Suc n)
  have " card {i. i < n \<and> i \<in> (\<lambda>i. i - b) ` (I - {0..<b})} =
  card {i. b \<le> i \<and> i < b + n \<and> i \<in> I}" 
    using Suc.hyps by blast
  show ?case
  proof(cases "b + n \<in> I")
    case True
    have "n \<in> (\<lambda>i. i - b) ` (I - {0..<b})" 
      by (metis Diff_iff True add_less_same_cancel1 atLeastLessThan_iff diff_add_inverse imageI zero_order(3))
    then have 1:"{i. i < Suc n \<and> i \<in> ((\<lambda> i. i - b) ` (I - {0..<b}))} = 
          {i. i < n \<and> i \<in> ((\<lambda> i. i - b) ` (I - {0..<b}))} \<union> {n}" 
      using less_Suc_eq by blast
    have 2: "{i. b \<le> i \<and> i < b + Suc n \<and> i \<in> I} = {i. b \<le> i \<and> i < b + n \<and> i \<in> I} \<union> {b + n}"
      using True    
      by force
    have "{i. i < n \<and> i \<in> ((\<lambda> i. i - b) ` (I - {0..<b}))} \<inter> {n} = {}" by auto
    then have "card {i. i < Suc n \<and> i \<in> ((\<lambda> i. i - b) ` (I - {0..<b}))} =
        card {i. i < n \<and> i \<in> ((\<lambda> i. i - b) ` (I - {0..<b}))} + card {n}"
      using 1 
      by force
    have "{i. b \<le> i \<and> i < b + n \<and> i \<in> I} \<inter> {b + n} = {}" by auto
    then have  "card {i. b \<le> i \<and> i < b + Suc n \<and> i \<in> I} = 
        card {i. b \<le> i \<and> i < b + n \<and> i \<in> I} + card {b + n}" using 2 
      by fastforce
    then show ?thesis 
      by (simp add: Suc.hyps \<open>card {i. i < Suc n \<and> i \<in> (\<lambda>i. i - b) ` (I - {0..<b})} = card {i. i < n \<and> i \<in> (\<lambda>i. i - b) ` (I - {0..<b})} + card {n}\<close>)
  next
    case False
    have "b + n \<notin> (I - {0..<b})" using False by auto
    then have "n \<notin> (\<lambda>i. i - b) ` (I - {0..<b})" 
      by auto
    then have "{i. i < Suc n \<and> i \<in> (\<lambda>i. i - b) ` (I - {0..<b})} = 
    {i. i < n \<and> i \<in> (\<lambda>i. i - b) ` (I - {0..<b})}" 
      using less_Suc_eq by blast
    have "{i. b \<le> i \<and> i < b + Suc n \<and> i \<in> I} = {i. b \<le> i \<and> i < b + n \<and> i \<in> I}" 
      using False less_Suc_eq by auto
    then show ?thesis 
      using Suc.hyps \<open>{i. i < Suc n \<and> i \<in> (\<lambda>i. i - b) ` (I - {0..<b})} = {i. i < n \<and> i \<in> (\<lambda>i. i - b) ` (I - {0..<b})}\<close> by presburger
  qed
 
qed

lemma fcdnwe:
   fixes A :: "'a  mat"
   assumes A: "A \<in> carrier_mat nr1 n" 
   assumes B: "B \<in> carrier_mat nr2 n"
   shows "submatrix (A @\<^sub>r B) I J =
          submatrix A I J @\<^sub>r submatrix B ((\<lambda> i. i - nr1) ` (I - {0..<nr1})) J"
proof 
  have "dim_row (submatrix (A @\<^sub>r B) I J) = card {i. i < dim_row (A @\<^sub>r B) \<and> i \<in> I}" 
    using dim_submatrix(1) by blast
  have "dim_row (A @\<^sub>r B)= nr1 + nr2" 
    using assms(1) assms(2) carrier_matD(1) by blast
  then have "{i. i < dim_row (A @\<^sub>r B) \<and> i \<in> I} = {i. i < nr1 + nr2  \<and> i \<in> I}"
  by presburger
   have "{i. i < nr1 + nr2  \<and> i \<in> I} = {0..<nr1+nr2} \<inter> I" 
     by fastforce
   then have "dim_row (submatrix (A @\<^sub>r B) I J) = card ({0..<nr1+nr2} \<inter> I)" 
     using \<open>dim_row (submatrix (A @\<^sub>r B) I J) = card {i. i < dim_row (A @\<^sub>r B) \<and> i \<in> I}\<close> \<open>{i. i < dim_row (A @\<^sub>r B) \<and> i \<in> I} = {i. i < nr1 + nr2 \<and> i \<in> I}\<close> by presburger
   have "dim_row (submatrix A I J) = card {i. i < nr1 \<and> i \<in> I}" 
     using assms(1) dim_submatrix(1) by blast
   have "dim_row (submatrix B ((\<lambda> i. i - nr1) ` (I - {0..<nr1})) J) = 
        card {i. i < nr2 \<and> i \<in> ((\<lambda> i. i - nr1) ` (I - {0..<nr1}))}"
     using assms(2) dim_submatrix(1) by blast
   have "card {i. i < nr2 \<and> i \<in> ((\<lambda> i. i - nr1) ` (I - {0..<nr1}))} = 
         card {i. i \<ge> nr1 \<and> i < nr1 + nr2 \<and> i \<in> I}" 
     using bowqbfq by blast
   have 1:"{i. i < nr1 + nr2  \<and> i \<in> I} = {i. i < nr1 \<and> i \<in> I} \<union> 
          {i. i \<ge> nr1 \<and> i < nr1 + nr2 \<and> i \<in> I}" 
     by force
   have "{i. i < nr1 \<and> i \<in> I} \<inter> {i. i \<ge> nr1 \<and> i < nr1 + nr2 \<and> i \<in> I} = {}" 
     by fastforce
   then have "card {i. i < nr1 + nr2  \<and> i \<in> I} = 
        card {i. i < nr1 \<and> i \<in> I} + card {i. i \<ge> nr1 \<and> i < nr1 + nr2 \<and> i \<in> I}"
     using 1 
     by (metis (mono_tags, lifting) \<open>{i. i < nr1 + nr2 \<and> i \<in> I} = {0..<nr1 + nr2} \<inter> I\<close> card_Un_disjoint finite_Int finite_Un finite_atLeastLessThan)
   have "dim_row (submatrix A I J @\<^sub>r submatrix B ((\<lambda> i. i - nr1) ` (I - {0..<nr1})) J) =
         dim_row (submatrix A I J) + dim_row (submatrix B ((\<lambda> i. i - nr1) ` (I - {0..<nr1})) J)"
     by (simp add: append_rows_def)
   have "dim_row (submatrix B ((\<lambda> i. i - nr1) ` (I - {0..<nr1})) J) = 
        card {i. i \<ge> nr1 \<and> i < nr1 + nr2 \<and> i \<in> I}" 
     using \<open>card {i. i < nr2 \<and> i \<in> (\<lambda>i. i - nr1) ` (I - {0..<nr1})} = card {i. nr1 \<le> i \<and> i < nr1 + nr2 \<and> i \<in> I}\<close> \<open>dim_row (submatrix B ((\<lambda>i. i - nr1) ` (I - {0..<nr1})) J) = card {i. i < nr2 \<and> i \<in> (\<lambda>i. i - nr1) ` (I - {0..<nr1})}\<close> by presburger
  
   show " dim_row (submatrix (A @\<^sub>r B) I J) = dim_row (submatrix A I J @\<^sub>r
                                submatrix B ((\<lambda>i. i - nr1) ` (I - {0..<nr1})) J)"
     using \<open>card {i. i < nr1 + nr2 \<and> i \<in> I} = card {i. i < nr1 \<and> i \<in> I} + card {i. nr1 \<le> i \<and> i < nr1 + nr2 \<and> i \<in> I}\<close> \<open>dim_row (submatrix (A @\<^sub>r B) I J) = card {i. i < dim_row (A @\<^sub>r B) \<and> i \<in> I}\<close> \<open>dim_row (submatrix A I J @\<^sub>r submatrix B ((\<lambda>i. i - nr1) ` (I - {0..<nr1})) J) = dim_row (submatrix A I J) + dim_row (submatrix B ((\<lambda>i. i - nr1) ` (I - {0..<nr1})) J)\<close> \<open>dim_row (submatrix A I J) = card {i. i < nr1 \<and> i \<in> I}\<close> \<open>dim_row (submatrix B ((\<lambda>i. i - nr1) ` (I - {0..<nr1})) J) = card {i. nr1 \<le> i \<and> i < nr1 + nr2 \<and> i \<in> I}\<close> \<open>{i. i < dim_row (A @\<^sub>r B) \<and> i \<in> I} = {i. i < nr1 + nr2 \<and> i \<in> I}\<close> by presburger
   
   have "dim_col (A @\<^sub>r B) = n"  
     using assms(1) assms(2) carrier_matD(2) by blast
   then have "dim_col (submatrix (A @\<^sub>r B) I J) =  card {j. j < n \<and> j \<in> J}"
     using dim_submatrix(2) 
     by blast
   have "dim_col (submatrix A I J) = card {j. j < n \<and> j \<in> J}"
     using dim_submatrix(2) 
     using assms(1) by blast
   have "dim_col (submatrix B ((\<lambda> i. i - nr1) ` (I - {0..<nr1})) J) = card {j. j < n \<and> j \<in> J}"
      using dim_submatrix(2) 
     using assms(2) by blast
   show "dim_col (submatrix (A @\<^sub>r B) I J) =
    dim_col (submatrix A I J @\<^sub>r submatrix B ((\<lambda>i. i - nr1) ` (I - {0..<nr1})) J)"
     by (smt (verit, best) \<open>dim_col (submatrix (A @\<^sub>r B) I J) = card {j. j < n \<and> j \<in> J}\<close> \<open>dim_col (submatrix A I J) = card {j. j < n \<and> j \<in> J}\<close> \<open>dim_col (submatrix B ((\<lambda>i. i - nr1) ` (I - {0..<nr1})) J) = card {j. j < n \<and> j \<in> J}\<close> carrier_append_rows carrier_matD(2) carrier_matI)

   fix i j
   assume asmi: "i < dim_row (submatrix A I J @\<^sub>r submatrix B ((\<lambda>i. i - nr1) ` (I - {0..<nr1})) J)"
   assume asmj: "j < dim_col (submatrix A I J @\<^sub>r submatrix B ((\<lambda>i. i - nr1) ` (I - {0..<nr1})) J)"
   have "submatrix (A @\<^sub>r B) I J $$ (i, j) = (A @\<^sub>r B) $$ (pick I i, pick J j)"
     by (metis (no_types, lifting) \<open>dim_col (submatrix (A @\<^sub>r B) I J) = dim_col (submatrix A I J @\<^sub>r submatrix B ((\<lambda>i. i - nr1) ` (I - {0..<nr1})) J)\<close> \<open>dim_row (submatrix (A @\<^sub>r B) I J) = dim_row (submatrix A I J @\<^sub>r submatrix B ((\<lambda>i. i - nr1) ` (I - {0..<nr1})) J)\<close> asmi asmj dim_submatrix(1) dim_submatrix(2) submatrix_index)
   show "submatrix (A @\<^sub>r B) I J $$ (i, j) =
           (submatrix A I J @\<^sub>r submatrix B ((\<lambda>i. i - nr1) ` (I - {0..<nr1})) J) $$ (i, j)" 
   proof(cases "i < dim_row (submatrix A I J)")
     case True
     have "(submatrix A I J @\<^sub>r submatrix B ((\<lambda>i. i - nr1) ` (I - {0..<nr1})) J) $$ (i, j) = 
          (submatrix A I J) $$ (i, j)" 
       by (smt (verit, best) Missing_Matrix.append_rows_nth(1) True \<open>dim_col (submatrix (A @\<^sub>r B) I J) = card {j. j < n \<and> j \<in> J}\<close> \<open>dim_col (submatrix (A @\<^sub>r B) I J) = dim_col (submatrix A I J @\<^sub>r submatrix B ((\<lambda>i. i - nr1) ` (I - {0..<nr1})) J)\<close> \<open>dim_col (submatrix A I J) = card {j. j < n \<and> j \<in> J}\<close> \<open>dim_col (submatrix B ((\<lambda>i. i - nr1) ` (I - {0..<nr1})) J) = card {j. j < n \<and> j \<in> J}\<close> asmi asmj carrier_matI index_row(1))
     have "(submatrix A I J) $$ (i, j) = A $$ (pick I i, pick J j)"
       by (metis (no_types, lifting) True \<open>dim_col (submatrix (A @\<^sub>r B) I J) = card {j. j < n \<and> j \<in> J}\<close> \<open>dim_col (submatrix (A @\<^sub>r B) I J) = dim_col (submatrix A I J @\<^sub>r submatrix B ((\<lambda>i. i - nr1) ` (I - {0..<nr1})) J)\<close> \<open>dim_col (submatrix A I J) = card {j. j < n \<and> j \<in> J}\<close> asmj dim_submatrix(1) dim_submatrix(2) submatrix_index)

     have 2: "pick I i < nr1"
       using True dim_submatrix(1) pick_le assms(1) 
       by (simp add: \<open>dim_row (submatrix A I J) = card {i. i < nr1 \<and> i \<in> I}\<close>)
     have "dim_col (A @\<^sub>r B) = dim_col A" 
       by (metis A \<open>dim_col (A @\<^sub>r B) = n\<close> carrier_matD(2))
     have "j < card {j. j < n \<and> j \<in> J}" using asmj 
       using \<open>dim_col (submatrix (A @\<^sub>r B) I J) = card {j. j < n \<and> j \<in> J}\<close> \<open>dim_col (submatrix (A @\<^sub>r B) I J) = dim_col (submatrix A I J @\<^sub>r submatrix B ((\<lambda>i. i - nr1) ` (I - {0..<nr1})) J)\<close> by presburger
     then have "pick J j < n" 
       using pick_le by blast
     then have "(A @\<^sub>r B) $$ (pick I i, pick J j) = A $$ (pick I i, pick J j)"
       using index_row(1) append_rows_nth(1)[OF A B 2]
       by (metis "2" A \<open>dim_col (A @\<^sub>r B) = dim_col A\<close> \<open>dim_col (A @\<^sub>r B) = n\<close> \<open>dim_row (A @\<^sub>r B) = nr1 + nr2\<close> carrier_matD(1) trans_less_add1)
     then show ?thesis 
       using \<open>(submatrix A I J @\<^sub>r submatrix B ((\<lambda>i. i - nr1) ` (I - {0..<nr1})) J) $$ (i, j) = submatrix A I J $$ (i, j)\<close> \<open>submatrix (A @\<^sub>r B) I J $$ (i, j) = (A @\<^sub>r B) $$ (pick I i, pick J j)\<close> \<open>submatrix A I J $$ (i, j) = A $$ (pick I i, pick J j)\<close> by presburger
   next
     case False
     have 3: "submatrix A I J \<in> carrier_mat (card {i. i < nr1 \<and> i \<in> I}) (card {j. j < n \<and> j \<in> J})"
       using \<open>dim_col (submatrix A I J) = card {j. j < n \<and> j \<in> J}\<close> \<open>dim_row (submatrix A I J) = card {i. i < nr1 \<and> i \<in> I}\<close> by blast
     have 4: "submatrix B ((\<lambda>i. i - nr1) ` (I - {0..<nr1})) J  \<in> 
               carrier_mat (card {i. i \<ge> nr1 \<and> i < nr1 + nr2 \<and> i \<in> I}) (card {j. j < n \<and> j \<in> J})"
       using \<open>dim_col (submatrix B ((\<lambda>i. i - nr1) ` (I - {0..<nr1})) J) = card {j. j < n \<and> j \<in> J}\<close> \<open>dim_row (submatrix B ((\<lambda>i. i - nr1) ` (I - {0..<nr1})) J) = card {i. nr1 \<le> i \<and> i < nr1 + nr2 \<and> i \<in> I}\<close> by blast
     have 5:"i < card {i. i < nr1 \<and> i \<in> I} + card {i. nr1 \<le> i \<and> i < nr1 + nr2 \<and> i \<in> I}"
       by (metis \<open>dim_row (submatrix A I J) = card {i. i < nr1 \<and> i \<in> I}\<close> \<open>dim_row (submatrix B ((\<lambda>i. i - nr1) ` (I - {0..<nr1})) J) = card {i. nr1 \<le> i \<and> i < nr1 + nr2 \<and> i \<in> I}\<close> append_rows_def asmi index_mat_four_block(2) index_zero_mat(2))
     have 6:"card {i. i < nr1 \<and> i \<in> I} \<le> i"  
       using False \<open>dim_row (submatrix A I J) = card {i. i < nr1 \<and> i \<in> I}\<close> by linarith
     have "(submatrix A I J @\<^sub>r submatrix B ((\<lambda>i. i - nr1) ` (I - {0..<nr1})) J) $$ (i, j) =
          (submatrix B ((\<lambda>i. i - nr1) ` (I - {0..<nr1})) J) $$ (i - card {i. i < nr1 \<and> i \<in> I}, j)"
   using append_rows_nth(2)[OF 3 4 6 5] False asmi
   by (smt (verit, ccfv_threshold) "3" "4" SNF_Missing_Lemmas.append_rows_nth \<open>dim_col (submatrix (A @\<^sub>r B) I J) = card {j. j < n \<and> j \<in> J}\<close> \<open>dim_col (submatrix (A @\<^sub>r B) I J) = dim_col (submatrix A I J @\<^sub>r submatrix B ((\<lambda>i. i - nr1) ` (I - {0..<nr1})) J)\<close> \<open>dim_row (submatrix A I J @\<^sub>r submatrix B ((\<lambda>i. i - nr1) ` (I - {0..<nr1})) J) = dim_row (submatrix A I J) + dim_row (submatrix B ((\<lambda>i. i - nr1) ` (I - {0..<nr1})) J)\<close> \<open>dim_row (submatrix A I J) = card {i. i < nr1 \<and> i \<in> I}\<close> \<open>dim_row (submatrix B ((\<lambda>i. i - nr1) ` (I - {0..<nr1})) J) = card {i. nr1 \<le> i \<and> i < nr1 + nr2 \<and> i \<in> I}\<close> asmj)
 
  have "(submatrix B ((\<lambda>i. i - nr1) ` (I - {0..<nr1})) J) $$ (i - card {i. i < nr1 \<and> i \<in> I}, j) = 
    B $$ (pick ((\<lambda>i. i - nr1) ` (I - {0..<nr1})) (i - card {i. i < nr1 \<and> i \<in> I}), pick J j)"
  by (metis (no_types, lifting) False \<open>dim_col (submatrix (A @\<^sub>r B) I J) = card {j. j < n \<and> j \<in> J}\<close> \<open>dim_col (submatrix (A @\<^sub>r B) I J) = dim_col (submatrix A I J @\<^sub>r submatrix B ((\<lambda>i. i - nr1) ` (I - {0..<nr1})) J)\<close> \<open>dim_col (submatrix B ((\<lambda>i. i - nr1) ` (I - {0..<nr1})) J) = card {j. j < n \<and> j \<in> J}\<close> \<open>dim_row (submatrix A I J @\<^sub>r submatrix B ((\<lambda>i. i - nr1) ` (I - {0..<nr1})) J) = dim_row (submatrix A I J) + dim_row (submatrix B ((\<lambda>i. i - nr1) ` (I - {0..<nr1})) J)\<close> \<open>dim_row (submatrix A I J) = card {i. i < nr1 \<and> i \<in> I}\<close> add_diff_inverse_nat asmi asmj dim_submatrix(1) dim_submatrix(2) nat_add_left_cancel_less submatrix_index)
 
  have "(submatrix (A @\<^sub>r B) I J) $$ (i, j) = (A @\<^sub>r B) $$ (pick I i, pick J j)"
    using \<open>submatrix (A @\<^sub>r B) I J $$ (i, j) = (A @\<^sub>r B) $$ (pick I i, pick J j)\<close> by fastforce
  have "i \<ge> card {i. i < nr1 \<and> i \<in> I}" 
    using "6" by fastforce
  then have "pick I i \<ge> pick I (card {i. i < nr1 \<and> i \<in> I})" 
    by (smt (verit, best) "5" IntE \<open>card {i. i < nr1 + nr2 \<and> i \<in> I} = card {i. i < nr1 \<and> i \<in> I} + card {i. nr1 \<le> i \<and> i < nr1 + nr2 \<and> i \<in> I}\<close> \<open>dim_row (submatrix A I J) = card {i. i < nr1 \<and> i \<in> I}\<close> \<open>{i. i < nr1 + nr2 \<and> i \<in> I} = {0..<nr1 + nr2} \<inter> I\<close> basic_trans_rules(21) card_mono dim_submatrix(1) le_eq_less_or_eq linorder_neqE_nat not_le not_less order.refl pick_mono_inf pick_mono_le subsetI)
  have "pick I (card {i. i < nr1 \<and> i \<in> I}) \<ge> nr1"
  proof(cases "infinite I")
    case True
    then show ?thesis  using fwfqwfpppjnb 
      by blast
  next
    case False
    have "{i. i < nr1 \<and> i \<in> I} \<subseteq> I" by auto
    then have "card {i. i < nr1 \<and> i \<in> I} < card I" 
      by (metis (mono_tags, lifting) "5" "6" Collect_empty_eq False card.empty card_seteq mem_Collect_eq nat_arith.rule0 not_le)
    then show ?thesis using fwfqwfpppjnb 
      by blast
  qed
  then have 7: "pick I i \<ge> nr1" 
    using \<open>pick I (card {i. i < nr1 \<and> i \<in> I}) \<le> pick I i\<close> basic_trans_rules(23) by blast
  have 8:"pick I i < nr1 + nr2" 
    using "5" \<open>card {i. i < nr1 + nr2 \<and> i \<in> I} = card {i. i < nr1 \<and> i \<in> I} + card {i. nr1 \<le> i \<and> i < nr1 + nr2 \<and> i \<in> I}\<close> pick_le by presburger
 have "j < card {j. j < n \<and> j \<in> J}" using asmj 
       using \<open>dim_col (submatrix (A @\<^sub>r B) I J) = card {j. j < n \<and> j \<in> J}\<close> \<open>dim_col (submatrix (A @\<^sub>r B) I J) = dim_col (submatrix A I J @\<^sub>r submatrix B ((\<lambda>i. i - nr1) ` (I - {0..<nr1})) J)\<close> by presburger
     then have "pick J j < n" 
       using pick_le by blast
  then have 9:"(A @\<^sub>r B) $$ (pick I i, pick J j) =  B $$ (pick I i - nr1, pick J j)"
    using append_rows_nth(2)[OF A B 7 8]
    by (metis "7" "8" B SNF_Missing_Lemmas.append_rows_nth assms(1) carrier_matD(1) not_le)

  have "i < card I \<or> infinite I" 
    by (metis IntE \<open>dim_row (submatrix (A @\<^sub>r B) I J) = card ({0..<nr1 + nr2} \<inter> I)\<close> \<open>dim_row (submatrix (A @\<^sub>r B) I J) = dim_row (submatrix A I J @\<^sub>r submatrix B ((\<lambda>i. i - nr1) ` (I - {0..<nr1})) J)\<close> asmi basic_trans_rules(21) card_mono not_le subsetI)
 then have "B $$ (pick ((\<lambda>i. i - nr1) ` (I - {0..<nr1})) (i - card {i. i < nr1 \<and> i \<in> I}), pick J j) = 
        B $$ (pick I i - nr1, pick J j)" using vwevwev 
   using "6" by presburger
  then show ?thesis 
    using 9 \<open>(submatrix A I J @\<^sub>r submatrix B ((\<lambda>i. i - nr1) ` (I - {0..<nr1})) J) $$ (i, j) = submatrix B ((\<lambda>i. i - nr1) ` (I - {0..<nr1})) J $$ (i - card {i. i < nr1 \<and> i \<in> I}, j)\<close> \<open>B $$ (pick ((\<lambda>i. i - nr1) ` (I - {0..<nr1})) (i - card {i. i < nr1 \<and> i \<in> I}), pick J j) = B $$ (pick I i - nr1, pick J j)\<close> \<open>submatrix (A @\<^sub>r B) I J $$ (i, j) = (A @\<^sub>r B) $$ (pick I i, pick J j)\<close> \<open>submatrix B ((\<lambda>i. i - nr1) ` (I - {0..<nr1})) J $$ (i - card {i. i < nr1 \<and> i \<in> I}, j) = B $$ (pick ((\<lambda>i. i - nr1) ` (I - {0..<nr1})) (i - card {i. i < nr1 \<and> i \<in> I}), pick J j)\<close> by presburger
qed
qed

   

lemma submatrix_inter_rows':
  shows "submatrix A I J = submatrix A (I \<inter> {0..<dim_row A}) J"
proof
  show "dim_row (submatrix A I J) = dim_row (submatrix A (I \<inter> {0..<dim_row A}) J)" 
    using dim_submatrix 
    by (smt (verit) Collect_cong Int_iff atLeastLessThan_iff less_nat_zero_code linorder_le_less_linear)

  show "dim_col (submatrix A I J) = dim_col (submatrix A (I \<inter> {0..<dim_row A}) J)" 
    using dim_submatrix 
    by (smt (verit) Collect_cong Int_iff atLeastLessThan_iff less_nat_zero_code linorder_le_less_linear)

  show "\<And>i j. i < dim_row (submatrix A (I \<inter> {0..<dim_row A}) J) \<Longrightarrow>
           j < dim_col (submatrix A (I \<inter> {0..<dim_row A}) J) \<Longrightarrow>
           submatrix A I J $$ (i, j) = submatrix A (I \<inter> {0..<dim_row A}) J $$ (i, j)" 
  proof -
    fix i j
    assume "i < dim_row (submatrix A (I \<inter> {0..<dim_row A}) J)" 
    assume "j < dim_col (submatrix A (I \<inter> {0..<dim_row A}) J)" 
    have "submatrix A I J $$ (i, j) = A $$ (pick I i, pick J j)"
      using submatrix_index
      by (metis (no_types, lifting) \<open>dim_row (submatrix A I J) = dim_row (submatrix A (I \<inter> {0..<dim_row A}) J)\<close>
          \<open>i < dim_row (submatrix A (I \<inter> {0..<dim_row A}) J)\<close> 
          \<open>j < dim_col (submatrix A (I \<inter> {0..<dim_row A}) J)\<close> dim_submatrix(1) dim_submatrix(2))
    have "{a. a < dim_row A \<and> a \<in> I} = (I \<inter> {0..<dim_row A})" 
      by fastforce
    have "i < card {a. a < dim_row A \<and> a \<in> I}"
      by (metis  \<open>dim_row (submatrix A I J) = dim_row (submatrix A (I \<inter> {0..<dim_row A}) J)\<close>
          \<open>i < dim_row (submatrix A (I \<inter> {0..<dim_row A}) J)\<close> dim_submatrix(1))

    then have "pick (I  \<inter> {0..<dim_row A}) i= pick I i"
      using pick_reduce_set[of i "dim_row A" I] `{a. a < dim_row A \<and> a \<in> I} = (I \<inter> {0..<dim_row A})`
      by presburger
    then show " submatrix A I J $$ (i, j) = submatrix A (I \<inter> {0..<dim_row A}) J $$ (i, j)"
      by (metis (no_types, lifting) \<open>i < dim_row (submatrix A (I \<inter> {0..<dim_row A}) J)\<close>
          \<open>j < dim_col (submatrix A (I \<inter> {0..<dim_row A}) J)\<close>
          \<open>submatrix A I J $$ (i, j) = A $$ (pick I i, pick J j)\<close>
          dim_submatrix(1) dim_submatrix(2) submatrix_index)
  qed
qed

lemma mat_delete_index':
  assumes A: "A \<in> carrier_mat (Suc nr) (Suc nc)"
      and i: "i < Suc nr" and j: "j < Suc nc"
      and i': "i' < nr" and j': "j' < nc"
  shows "A $$ (insert_index i i', insert_index j j') = mat_delete A i j $$ (i', j')"
  unfolding mat_delete_def
  unfolding permutation_insert_expand
  unfolding insert_index_def
  using A i j i' j' by auto




lemma gbergre:
  fixes A :: "'a  mat"
  assumes A: "A \<in> carrier_mat nr n"
  assumes b: "b \<in> carrier_vec (dim_col B)"
  assumes "B = submatrix A I J" 
  assumes "j < dim_col B" 
  shows "mat_delete (B @\<^sub>r mat_of_rows (dim_col B) [b]) (dim_row B) j = 
         submatrix A I (J - {pick J j})"
proof
  show " dim_row (mat_delete (B @\<^sub>r mat_of_rows (dim_col B) [b]) (dim_row B) j) =
    dim_row (submatrix A I (J - {pick J j}))" 
    by (simp add: append_rows_def assms(3) dim_submatrix(1))
  have "dim_col (B @\<^sub>r mat_of_rows (dim_col B) [b]) = dim_col B"
    by (meson carrier_append_rows carrier_matD(2) carrier_matI mat_of_rows_carrier(1))
  then have "dim_col (mat_delete (B @\<^sub>r mat_of_rows (dim_col B) [b]) (dim_row B) j) =
      dim_col B - 1" using mat_delete_dim(2) 
    by metis 
  have " dim_col (submatrix A I (J - {pick J j})) = card {i. i < dim_col A \<and> i \<in> (J - {pick J j})}"
    using dim_submatrix(2)[of A I "J - {pick J j}"] 
    by blast
  have "dim_col B = card {i. i < dim_col A \<and> i \<in> J}" 
    using assms(3) dim_submatrix(2) by blast 
  have "j < card {i. i < dim_col A \<and> i \<in> J}" 
    using \<open>dim_col B = card {i. i < dim_col A \<and> i \<in> J}\<close> assms(4) by presburger
  have "{i. i < dim_col A \<and> i \<in> J} \<subseteq> J" 
    by fastforce
 
  have "{i. i < dim_col A \<and> i \<in> J} = {i. i < dim_col A \<and> i \<in> (J - {pick J j})} \<union> {pick J j}"
    apply safe
    using \<open>dim_col B = card {i. i < dim_col A \<and> i \<in> J}\<close> assms(4) pick_le apply presburger
    apply(cases "infinite J")
    apply (simp add: pick_in_set_inf)
    by (meson \<open>j < card {i. i < dim_col A \<and> i \<in> J}\<close> \<open>{i. i < dim_col A \<and> i \<in> J} \<subseteq> J\<close> basic_trans_rules(22) card_mono pick_in_set)
  
  then have "card {i. i < dim_col A \<and> i \<in> J} - 1 = card {i. i < dim_col A \<and> i \<in> (J - {pick J j})}"
    by force
  

  show "dim_col (mat_delete (B @\<^sub>r mat_of_rows (dim_col B) [b]) (dim_row B) j) =
    dim_col (submatrix A I (J - {pick J j}))" 
    by (metis \<open>card {i. i < dim_col A \<and> i \<in> J} - 1 = card {i. i < dim_col A \<and> i \<in> J - {pick J j}}\<close> \<open>dim_col (mat_delete (B @\<^sub>r mat_of_rows (dim_col B) [b]) (dim_row B) j) = dim_col B - 1\<close> \<open>dim_col (submatrix A I (J - {pick J j})) = card {i. i < dim_col A \<and> i \<in> J - {pick J j}}\<close> \<open>dim_col B = card {i. i < dim_col A \<and> i \<in> J}\<close>)

  fix i k
  assume asmi: "i < dim_row (submatrix A I (J - {pick J j}))"
  assume asmk: "k < dim_col (submatrix A I (J - {pick J j}))"
  have asmi': "i < dim_row (mat_delete (B @\<^sub>r mat_of_rows (dim_col B) [b]) (dim_row B) j)" 
    using \<open>dim_row (mat_delete (B @\<^sub>r mat_of_rows (dim_col B) [b]) (dim_row B) j) = dim_row (submatrix A I (J - {pick J j}))\<close> asmi by linarith
  have asmk': "k < dim_col (mat_delete (B @\<^sub>r mat_of_rows (dim_col B) [b]) (dim_row B) j)" 
    using \<open>dim_col (mat_delete (B @\<^sub>r mat_of_rows (dim_col B) [b]) (dim_row B) j) = dim_col (submatrix A I (J - {pick J j}))\<close> asmk by presburger
  have " (B @\<^sub>r mat_of_rows (dim_col B) [b]) \<in> carrier_mat (dim_row B + 1) (dim_col B)" 
    by (metis Num.numeral_nat(7) add_0 carrier_append_rows carrier_matI list.size(3) list.size(4) mat_of_rows_carrier(1))

 show "mat_delete (B @\<^sub>r mat_of_rows (dim_col B) [b]) (dim_row B) j $$ (i, k) =
         submatrix A I (J - {pick J j}) $$ (i, k)"
 proof(cases "dim_col B = 0")
   case True
   then show ?thesis 
     using assms(4) by linarith
 next
   case False
   have 1:"j < Suc (dim_col B - 1)" 
     using assms(4) by linarith 
   have 2: "i < dim_row B" 
     by (metis asmi assms(3) dim_submatrix(1))
   have 3: "k < dim_col B - 1" 
     using \<open>dim_col (mat_delete (B @\<^sub>r mat_of_rows (dim_col B) [b]) (dim_row B) j) = dim_col (submatrix A I (J - {pick J j}))\<close> \<open>dim_col (mat_delete (B @\<^sub>r mat_of_rows (dim_col B) [b]) (dim_row B) j) = dim_col B - 1\<close> asmk by presburger
   have 4:" B @\<^sub>r mat_of_rows (dim_col B) [b] \<in> carrier_mat (Suc (dim_row B)) (Suc (dim_col B - 1))"
     by (metis "3" Suc_eq_plus1 \<open>B @\<^sub>r mat_of_rows (dim_col B) [b] \<in> carrier_mat (dim_row B + 1) (dim_col B)\<close> add_diff_inverse_nat less_nat_zero_code nat_diff_split_asm plus_1_eq_Suc)
   have 5: "dim_row B < Suc (dim_row B)" 
     by blast
   have "mat_delete (B @\<^sub>r mat_of_rows (dim_col B) [b]) (dim_row B) j $$ (i, k) =
            (B @\<^sub>r mat_of_rows (dim_col B) [b]) $$ (insert_index (dim_row B) i, insert_index j k)" 
     using mat_delete_index'[OF 4 5 1 2 3]
     by presburger
   have "insert_index (dim_row B) i = i" 
     using 2 insert_index(1) by blast
   have "(B @\<^sub>r mat_of_rows (dim_col B) [b]) $$ (insert_index (dim_row B) i, insert_index j k) =
      (B @\<^sub>r mat_of_rows (dim_col B) [b]) $$ (i, insert_index j k)"
     using \<open>insert_index (dim_row B) i = i\<close> by presburger
   have "(B @\<^sub>r mat_of_rows (dim_col B) [b]) $$ (i, insert_index j k) = 
        B $$ (i, insert_index j k)"
     by (smt (verit, best) "2" "4" Missing_Matrix.append_rows_nth(1) Suc_eq_plus1 \<open>dim_col (B @\<^sub>r mat_of_rows (dim_col B) [b]) = dim_col B\<close> \<open>dim_col (mat_delete (B @\<^sub>r mat_of_rows (dim_col B) [b]) (dim_row B) j) = dim_col B - 1\<close> asmk' carrier_matD(1) carrier_matD(2) carrier_matI index_row(1) insert_index_def mat_of_rows_carrier(1) nat_add_left_cancel_less plus_1_eq_Suc trans_less_add1)
   then have 6: "mat_delete (B @\<^sub>r mat_of_rows (dim_col B) [b]) (dim_row B) j $$ (i, k) =
      B $$ (i, insert_index j k)"
     using \<open>insert_index (dim_row B) i = i\<close> \<open>mat_delete (B @\<^sub>r mat_of_rows (dim_col B) [b]) (dim_row B) j $$ (i, k) = (B @\<^sub>r mat_of_rows (dim_col B) [b]) $$ (insert_index (dim_row B) i, insert_index j k)\<close> by presburger
   obtain i' where i':"row A i' = row (submatrix A I UNIV) i \<and> i' < dim_row A \<and> i' = pick I i"
     by (metis (full_types) asmi dim_submatrix(1) pick_le row_submatrix_UNIV)
   have "insert_index j k < dim_col B" 
     by (metis "3" "4" \<open>dim_col (B @\<^sub>r mat_of_rows (dim_col B) [b]) = dim_col B\<close> basic_trans_rules(20) carrier_matD(2) insert_index_def not_less_eq)
   obtain k1 where k1: "col A k1 = col (submatrix A UNIV J) (insert_index j k) \<and> k1 < dim_col A \<and> k1 = pick J (insert_index j k)" 
     using asmk  pick_le col_submatrix_UNIV 
     by (metis (no_types, lifting) Collect_cong \<open>dim_col B = card {i. i < dim_col A \<and> i \<in> J}\<close> \<open>insert_index j k < dim_col B\<close>)

   
   obtain k2 where k2: "col A k2 = col (submatrix A UNIV (J - {pick J j})) k \<and> k2 < dim_col A \<and> k2 = pick (J - {pick J j}) k"
         using asmk dim_submatrix(2) pick_le col_submatrix_UNIV 
         by (metis (no_types, lifting) Collect_cong)

       have 7: "B = submatrix (submatrix A I UNIV) UNIV J" 
         using assms(3) submatrix_split2 by blast
       have "B $$ (i, insert_index j k) = A $$ (pick I i, pick J (insert_index j k))"
         apply(simp only: assms(3))
         by (metis (no_types, lifting) \<open>insert_index j k < dim_col B\<close> asmi assms(3) dim_submatrix(1) dim_submatrix(2) submatrix_index)
       have "B $$ (i, insert_index j k) = A $$ (i', k1)" 
         using \<open>B $$ (i, insert_index j k) = A $$ (pick I i, pick J (insert_index j k))\<close> i' k1 by blast
       have "submatrix A I (J - {pick J j}) $$ (i, k) = A $$ (i', k2)"
         by (metis (no_types, lifting) asmi asmk dim_submatrix(1) dim_submatrix(2) i' k2 submatrix_index)
     
 
         have "pick J (insert_index j k) = pick (J - {pick J j}) k"
       proof(cases "k < j")
         case True
         have "pick J (insert_index j k) = pick J k" unfolding insert_index_def 
           using True 
           by simp
      
         have "pick J k \<in> J - {pick J j}" 
           by (smt (verit, del_insts) DiffI True \<open>dim_col B = card {i. i < dim_col A \<and> i \<in> J}\<close> \<open>insert_index j k < dim_col B\<close> \<open>{i. i < dim_col A \<and> i \<in> J} \<subseteq> J\<close> assms(4) card_mono insert_index(1) nat_neq_iff order_less_le_trans pick_eq_iff_inf pick_in_set_inf pick_in_set_le pick_mono_le singletonD)
         then have "pick (J - {pick J j}) (card {a\<in>(J - {pick J j}). a < pick J k}) = pick J k" 
           using pick_card_in_set 
           by presburger
         have "card {a\<in>J. a < pick J k} = k" 
           by (metis True \<open>dim_col B = card {i. i < dim_col A \<and> i \<in> J}\<close> \<open>insert_index j k < dim_col B\<close> \<open>{i. i < dim_col A \<and> i \<in> J} \<subseteq> J\<close> card_mono card_pick insert_index(1) order_trans_rules(22))
         
         have "pick J k < pick J j" 
           by (metis True \<open>dim_col B = card {i. i < dim_col A \<and> i \<in> J}\<close> \<open>{i. i < dim_col A \<and> i \<in> J} \<subseteq> J\<close> assms(4) card_mono order_trans_rules(22) pick_mono_inf pick_mono_le)

         then  have "{a\<in>J. a < pick J k} = {a\<in>(J - {pick J j}). a < pick J k}"
           by auto
        
         then have "pick (J - {pick J j}) k = pick J k" 
           using \<open>card {a \<in> J. a < pick J k} = k\<close> \<open>pick (J - {pick J j}) (card {a \<in> J - {pick J j}. a < pick J k}) = pick J k\<close> by presburger
         then show ?thesis 
           using \<open>pick J (insert_index j k) = pick J k\<close> by presburger
       next
         case False
         have "pick J (insert_index j k) = pick J (Suc k)" 
           using False insert_index_def by presburger
         show ?thesis
         proof(cases "k = j")
           case True
           have "pick J (Suc k) = pick J (Suc j)"
             using True by fastforce
           have "j < dim_col B - 1"
             using "3" True by blast
           then show ?thesis using pick_suc_diff_set 
             by (metis False True \<open>dim_col B = card {i. i < dim_col A \<and> i \<in> J}\<close> \<open>insert_index j k < dim_col B\<close> \<open>{i. i < dim_col A \<and> i \<in> J} \<subseteq> J\<close> basic_trans_rules(22) card_mono insert_index_def)
         next
           case False
           have "k > j" using `\<not> k < j` False 
             using nat_neq_iff by blast
           then have "pick J k > pick J j" 
             by (metis Suc_lessD \<open>dim_col B = card {i. i < dim_col A \<and> i \<in> J}\<close> \<open>insert_index j k < dim_col B\<close> \<open>{i. i < dim_col A \<and> i \<in> J} \<subseteq> J\<close> basic_trans_rules(22) card_mono insert_index_def pick_mono_inf pick_mono_le)

           have "pick J k \<in> J - {pick J j}" 
             by (metis (no_types, lifting) DiffI \<open>dim_col B = card {i. i < dim_col A \<and> i \<in> J}\<close> \<open>insert_index j k < dim_col B\<close> \<open>pick J j < pick J k\<close> \<open>{i. i < dim_col A \<and> i \<in> J} \<subseteq> J\<close> basic_trans_rules(22) card_mono insert_index_def le_eq_less_or_eq lessI nat_neq_iff pick_in_set_inf pick_in_set_le singletonD)
           then have 1: "pick (J - {pick J j}) (card {a\<in>(J - {pick J j}). a < pick J k}) = pick J k"
           using pick_card_in_set 
           by presburger
         have "{a\<in>(J - {pick J j}). a < pick J k} \<union> {pick J j} = {a\<in>J. a < pick J k}"
           apply safe
           apply (metis Diff_empty Diff_insert0 \<open>card {i. i < dim_col A \<and> i \<in> J} - 1 = card {i. i < dim_col A \<and> i \<in> J - {pick J j}}\<close> \<open>dim_col (submatrix A I (J - {pick J j})) = card {i. i < dim_col A \<and> i \<in> J - {pick J j}}\<close> \<open>dim_col B = card {i. i < dim_col A \<and> i \<in> J}\<close> assms(3) assms(4) diff_less less_nat_zero_code order.irrefl semiring_norm(135) zero_less_iff_neq_zero)
           by (simp add: \<open>pick J j < pick J k\<close>)
         have "pick J j \<notin> {a\<in>(J - {pick J j}). a < pick J k}"
           by blast
         have "card {a\<in>J. a < pick J k} = k" 
           by (metis Suc_lessD \<open>dim_col B = card {i. i < dim_col A \<and> i \<in> J}\<close> \<open>insert_index j k < dim_col B\<close> \<open>j < k\<close> \<open>{i. i < dim_col A \<and> i \<in> J} \<subseteq> J\<close> basic_trans_rules(19) card_mono card_pick card_pick_le  insert_index(2) insert_index_def linorder_neqE_nat n_not_Suc_n not_less_iff_gr_or_eq)
         have "card ({a\<in>(J - {pick J j}). a < pick J k} \<union> {pick J j}) = card {a\<in>(J - {pick J j}). a < pick J k} + card {pick J j}"
           by force
         then have "card {a\<in>(J - {pick J j}). a < pick J k} + 1 = card {a\<in>J. a < pick J k}"
           by (metis \<open>{a \<in> J - {pick J j}. a < pick J k} \<union> {pick J j} = {a \<in> J. a < pick J k}\<close> card_eq_1_iff)
         then have "card {a\<in>(J - {pick J j}). a < pick J k} = k - 1" 
           using \<open>card {a \<in> J. a < pick J k} = k\<close> by presburger
         then have "pick (J - {pick J j}) (k - 1) = pick J k" using 1 
           by presburger
         have "pick (J - {pick J j}) (Suc (k - 1)) = (LEAST a. a \<in> (J - {pick J j}) \<and> pick (J - {pick J j}) (k - 1) < a)" 
           using DL_Missing_Sublist.pick.simps(2) by blast
         have "pick J (Suc k) = (LEAST a. a \<in> J \<and> pick J k < a)"
           using DL_Missing_Sublist.pick.simps(2) by blast
         have "(LEAST a. a \<in> (J - {pick J j}) \<and> pick (J - {pick J j}) (k - 1) < a) = 
              (LEAST a. a \<in> J \<and> pick J k < a)" 
           by (metis Diff_iff \<open>pick (J - {pick J j}) (k - 1) = pick J k\<close> \<open>pick J j < pick J k\<close> basic_trans_rules(19) less_not_refl2 singletonD)
         then have "pick (J - {pick J j}) k = pick J (Suc k)" 
           by (metis Suc_eq_plus1 \<open>card {a \<in> J - {pick J j}. a < pick J k} + 1 = card {a \<in> J. a < pick J k}\<close> \<open>card {a \<in> J - {pick J j}. a < pick J k} = k - 1\<close> \<open>card {a \<in> J. a < pick J k} = k\<close> \<open>pick (J - {pick J j}) (Suc (k - 1)) = (LEAST a. a \<in> J - {pick J j} \<and> pick (J - {pick J j}) (k - 1) < a)\<close> \<open>pick J (Suc k) = (LEAST a. a \<in> J \<and> pick J k < a)\<close>)
       
         then show ?thesis 
           using \<open>pick J (insert_index j k) = pick J (Suc k)\<close> by presburger
       qed
     qed

 
       then have "k1 = k2" using k1 k2 
         by blast 
       then show ?thesis 
         using "6" \<open>B $$ (i, insert_index j k) = A $$ (i', k1)\<close> \<open>submatrix A I (J - {pick J j}) $$ (i, k) = A $$ (i', k2)\<close> by presburger
     qed
   qed

lemma fwqfqwfojj:
  assumes "b \<in> carrier_vec n"
  shows "submatrix (mat_of_rows n [b]) {0} J =
         mat_of_rows (card ({0..<n} \<inter> J)) [vec_of_list (nths (list_of_vec (b)) J)]"
proof
  have "dim_row (mat_of_rows n [b]) = 1"
    by simp
  have 1:"dim_row (submatrix (mat_of_rows n [b]) {0} J) = 
          card {i. i < dim_row (mat_of_rows n [b]) \<and> i \<in> {0}}" 
    using dim_submatrix(1) by blast
  have "{i. i < dim_row (mat_of_rows n [b]) \<and> i \<in> {0}} = {0}"
    by auto
  then have "dim_row (submatrix (mat_of_rows n [b]) {0} J) = 1"
    by (simp add: "1")
  then show "dim_row (submatrix (mat_of_rows n [b]) {0} J) =
    dim_row (mat_of_rows (card ({0..<n} \<inter> J))  [vec_of_list (nths (list_of_vec b) J)])"
    by simp 
  have "dim_col (submatrix (mat_of_rows n [b]) {0} J) = 
      card {j. j < dim_col (mat_of_rows n [b]) \<and> j \<in> J}"
    by (simp add: dim_submatrix(2))
  have "{j. j < dim_col (mat_of_rows n [b]) \<and> j \<in> J} = 
        {j. j < n \<and> j \<in> J}" 
    by auto
  then have "{j. j < n \<and> j \<in> J} = {0..<n} \<inter> J" by auto
  then have "card {j. j < dim_col (mat_of_rows n [b]) \<and> j \<in> J} = (card ({0..<n} \<inter> J))" 
    using \<open>{j. j < dim_col (mat_of_rows n [b]) \<and> j \<in> J} = {j. j < n \<and> j \<in> J}\<close> by presburger
  then show "dim_col (submatrix (mat_of_rows n [b]) {0} J) =
         dim_col (mat_of_rows (card ({0..<n} \<inter> J)) [vec_of_list (nths (list_of_vec b) J)])"
    by (simp add: \<open>dim_col (submatrix (mat_of_rows n [b]) {0} J) = card {j. j < dim_col (mat_of_rows n [b]) \<and> j \<in> J}\<close>)

  fix i
  fix j
  assume "i < dim_row (mat_of_rows (card ({0..<n} \<inter> J)) [vec_of_list (nths (list_of_vec b) J)])"
  assume "j < dim_col (mat_of_rows (card ({0..<n} \<inter> J)) [vec_of_list (nths (list_of_vec b) J)])"
  have "i = 0" 
    by (metis Num.numeral_nat(7) Suc_eq_plus1 \<open>i < dim_row (mat_of_rows (card ({0..<n} \<inter> J)) [vec_of_list (nths (list_of_vec b) J)])\<close> less_one list.size(3) list.size(4) mat_of_rows_carrier(2))
  have "j < (card ({0..<n} \<inter> J))" 
    using \<open>card {j. j < dim_col (mat_of_rows n [b]) \<and> j \<in> J} = card ({0..<n} \<inter> J)\<close> \<open>dim_col (submatrix (mat_of_rows n [b]) {0} J) = card {j. j < dim_col (mat_of_rows n [b]) \<and> j \<in> J}\<close> \<open>dim_col (submatrix (mat_of_rows n [b]) {0} J) = dim_col (mat_of_rows (card ({0..<n} \<inter> J)) [vec_of_list (nths (list_of_vec b) J)])\<close> \<open>j < dim_col (mat_of_rows (card ({0..<n} \<inter> J)) [vec_of_list (nths (list_of_vec b) J)])\<close> by presburger
  have "row (submatrix (mat_of_rows n [b]) {0} J) 0 = col (submatrix (mat_of_rows n [b]) {0} J)\<^sup>T 0" 
    by (simp add: \<open>dim_row (submatrix (mat_of_rows n [b]) {0} J) = 1\<close>)


  have "mat_of_rows (card ({0..<n} \<inter> J)) [vec_of_list (nths (list_of_vec b) J)] $$ (i, j) =
       vec_of_list (nths (list_of_vec b) J) $ j"
    by (metis One_nat_def Suc_eq_plus1 \<open>i = 0\<close> \<open>j < card ({0..<n} \<inter> J)\<close> list.size(3) list.size(4) mat_of_rows_index nth_Cons_0 zero_less_one_class.zero_less_one)

  have "vec_of_list (nths (list_of_vec b) J) $ j = b $ (pick J j)" 
  proof -
    have f1: "card ({0..<n} \<inter> J) = card {na. na < n \<and> na \<in> J}"
      by (smt (z3) \<open>card {j. j < dim_col (mat_of_rows n [b]) \<and> j \<in> J} = card ({0..<n} \<inter> J)\<close> \<open>{j. j < dim_col (mat_of_rows n [b]) \<and> j \<in> J} = {j. j < n \<and> j \<in> J}\<close>)
    have f2: "j < card ({0..<n} \<inter> J)"
      using \<open>j < card ({0..<n} \<inter> J)\<close> by fastforce
    have "dim_vec b = n"
      by (smt (z3) assms carrier_vecD)
    then show ?thesis
      using f2 f1 by (simp add: list_of_vec_index nth_nths)
  qed

  have "submatrix (mat_of_rows n [b]) {0} J $$ (i, j) = (mat_of_rows n [b]) $$ (pick {0} i, pick J j)" 
    by (metis (no_types, lifting) \<open>card {j. j < dim_col (mat_of_rows n [b]) \<and> j \<in> J} = card ({0..<n} \<inter> J)\<close> \<open>dim_col (submatrix (mat_of_rows n [b]) {0} J) = card {j. j < dim_col (mat_of_rows n [b]) \<and> j \<in> J}\<close> \<open>dim_row (submatrix (mat_of_rows n [b]) {0} J) = 1\<close> \<open>i = 0\<close> \<open>j < card ({0..<n} \<inter> J)\<close> dim_submatrix(1) dim_submatrix(2) submatrix_index zero_less_one_class.zero_less_one)
  have "(mat_of_rows n [b]) $$ (pick {0} i, pick J j) = b $ (pick J j)" 
    by (metis "1" One_nat_def Suc_eq_plus1 \<open>dim_row (mat_of_rows n [b]) = 1\<close> \<open>dim_row (submatrix (mat_of_rows n [b]) {0} J) = 1\<close> \<open>i = 0\<close> \<open>j < card ({0..<n} \<inter> J)\<close> \<open>{j. j < n \<and> j \<in> J} = {0..<n} \<inter> J\<close> less_one list.size(3) list.size(4) mat_of_rows_index nth_Cons_0 pick_le)
  show "submatrix (mat_of_rows n [b]) {0} J $$ (i, j) =
           mat_of_rows (card ({0..<n} \<inter> J)) [vec_of_list (nths (list_of_vec b) J)] $$ (i, j)"
    using \<open>mat_of_rows (card ({0..<n} \<inter> J)) [vec_of_list (nths (list_of_vec b) J)] $$ (i, j) = vec_of_list (nths (list_of_vec b) J) $v j\<close> \<open>mat_of_rows n [b] $$ (pick {0} i, pick J j) = b $v pick J j\<close> \<open>submatrix (mat_of_rows n [b]) {0} J $$ (i, j) = mat_of_rows n [b] $$ (pick {0} i, pick J j)\<close> \<open>vec_of_list (nths (list_of_vec b) J) $v j = b $v pick J j\<close> by presburger
qed

lemma fhqwpfh:
  assumes "finite S" 
  assumes "a \<in> S"
  assumes "\<forall> x \<in> S. x \<noteq> a \<longrightarrow> f x = 0"
  shows "sum f S = f a" 
  by (metis (mono_tags, opaque_lifting) Diff_iff add.right_neutral assms(1) assms(2) assms(3) insert_iff sum.neutral sum.remove)


lemma bcqkcbpqw:
shows "submatrix A {} J = 0\<^sub>m 0 (dim_col (submatrix A {} J))"
  unfolding submatrix_def 
  apply rule
  by simp+

lemma fpfhpqwfcqw:
 fixes A :: "'a  mat"
 assumes A: "A \<in> carrier_mat nr nc" 
 assumes "b \<in> carrier_vec nc" 
 assumes "B = A @\<^sub>r mat_of_rows nc [b]"
 shows "row B nr = b" 
  by (smt (verit, del_insts) add.right_neutral add_Suc_right assms(1) assms(2) assms(3) diff_add_inverse gram_schmidt.append_rows_index_same' le_refl length_nth_simps(3) lessI list.size(3) list.size(4) mat_of_rows_carrier(1) mat_of_rows_row)


lemma tot_unimod_append_unit_vec:
 fixes A :: "'a  mat"
   assumes A: "A \<in> carrier_mat nr n" 
   assumes "tot_unimodular A"
   shows "tot_unimodular (A @\<^sub>r mat_of_rows n [unit_vec n i])" (is "tot_unimodular ?A'")
  unfolding tot_unimodular_def
proof rule
  fix B
  show " (\<exists>I J. submatrix (A @\<^sub>r mat_of_rows n [unit_vec n i])I J = B) \<longrightarrow> det B \<in> {- 1, 0, 1}" 
  proof
  assume asm:"\<exists>I J. submatrix (A @\<^sub>r mat_of_rows n [unit_vec n i]) I J = B"
  then show "det B \<in> {-1,0,1}" 
  proof(cases "dim_row B \<noteq> dim_col B")
    case True
    then show ?thesis unfolding Determinant.det_def 
      by (meson insertCI)
  next
    case False
    then  have "dim_row B = dim_col B" by auto
    obtain I J where I_J: "submatrix (A @\<^sub>r mat_of_rows n [unit_vec n i]) I J = B"
      using asm by presburger
    have 1: "mat_of_rows n [unit_vec n i] \<in> carrier_mat 1 n" 
      using mat_of_rows_carrier(1)[of n "[unit_vec n i]"] 
      by auto
    have "row ?A' nr = unit_vec n i" 
      using append_rows_nth(2)[OF A 1] mat_of_rows_row by simp 
    have 2: "B \<in> carrier_mat (dim_row B) (dim_row B)" 
      by (metis False carrier_matI)
    let ?f = "(\<lambda> i. i - nr)"

    have 10:"B = submatrix A I J @\<^sub>r submatrix (mat_of_rows n [unit_vec n i]) (?f ` (I - {0..<nr})) J"
      using fcdnwe[OF A 1]
      using I_J by blast


    show ?thesis 
    proof(cases "nr \<in> I")
      case True
      have "{ia. ia < dim_row (A @\<^sub>r mat_of_rows n [unit_vec n i]) \<and> ia \<in> I} \<noteq> {}"
        by (smt (verit, del_insts) Collect_empty_eq True add.right_neutral add_Suc_right 
            append_rows_def assms(1) carrier_matD(1) index_mat_four_block(2) index_zero_mat(2)
            lessI list.size(3) list.size(4) mat_of_rows_carrier(2))
      have "finite {ia. ia < dim_row (A @\<^sub>r mat_of_rows n [unit_vec n i]) \<and> ia \<in> I}"
        using finite_nat_set_iff_bounded by blast
      then have "card {ia. ia < dim_row (A @\<^sub>r mat_of_rows n [unit_vec n i]) \<and> ia \<in> I} > 0"
        using \<open>{ia. ia < dim_row (A @\<^sub>r mat_of_rows n [unit_vec n i]) \<and> ia \<in> I} \<noteq> {}\<close> card_gt_0_iff by blast
      then have "dim_row (submatrix ?A' I J) > 0" 
          using dim_submatrix(1)[of ?A' I J]  
          by linarith
      then have "dim_row B - 1 < dim_row B" 
        using I_J diff_less verit_comp_simplify(28) by blast
      have 4: "det B = (\<Sum>j<dim_row B. B $$ (dim_row B - 1,j) * cofactor B (dim_row B - 1) j)"
        using laplace_expansion_row[OF 2] 
        using \<open>dim_row B - 1 < dim_row B\<close> by blast
      have 3:"dim_row (mat_of_rows n [unit_vec n i]) =  1" using 1 
        by fast
      have "submatrix (mat_of_rows n [unit_vec n i]) (?f ` (I - {0..<nr})) J =
            submatrix (mat_of_rows n [unit_vec n i]) (?f ` (I - {0..<nr})\<inter>{0..<1}) J"
        using submatrix_inter_rows' 3 
        by metis
      have "?f ` (I - {0..<nr}) \<inter> {0..<1} = {0}" 
        apply safe 
          apply simp+
         apply (metis DiffI True atLeastLessThan_iff diff_self_eq_0 image_iff less_irrefl)
        by simp
      have "submatrix (mat_of_rows n [unit_vec n i]) (?f ` (I - {0..<nr})) J =
          submatrix (mat_of_rows n [unit_vec n i]) {0} J" 
        by (metis \<open>(\<lambda>i. i - nr) ` (I - {0..<nr}) \<inter> {0..<1} = {0}\<close>
            \<open>submatrix (mat_of_rows n [unit_vec n i]) ((\<lambda>i. i - nr) ` (I - {0..<nr})) J = submatrix (mat_of_rows n [unit_vec n i]) ((\<lambda>i. i - nr) ` (I - {0..<nr}) \<inter> {0..<1}) J\<close>)
      have "B = submatrix A I J @\<^sub>r submatrix (mat_of_rows n [unit_vec n i]) {0} J" 
        by (simp add: \<open>B = submatrix A I J @\<^sub>r submatrix (mat_of_rows n [unit_vec n i]) ((\<lambda>i. i - nr) ` (I - {0..<nr})) J\<close>
            \<open>submatrix (mat_of_rows n [unit_vec n i]) ((\<lambda>i. i - nr) ` (I - {0..<nr})) J = submatrix (mat_of_rows n [unit_vec n i]) {0} J\<close>)
      have "B = submatrix A I J @\<^sub>r mat_of_rows (card ({0..<n} \<inter> J)) [vec_of_list (nths (list_of_vec (unit_vec n i)) J)]"
        by (simp add: \<open>B = submatrix A I J @\<^sub>r submatrix (mat_of_rows n [unit_vec n i]) {0} J\<close> fwqfqwfojj)
    
      have "row (submatrix A I J @\<^sub>r mat_of_rows (card ({0..<n} \<inter> J)) [vec_of_list (nths (list_of_vec (unit_vec n i)) J)]) 
        (dim_row (submatrix A I J)) = vec_of_list (nths (list_of_vec (unit_vec n i)) J)"
        using fpfhpqwfcqw[of "submatrix A I J" "card ({0..<nr} \<inter> I)" "card ({0..<n} \<inter> J)" "vec_of_list (nths (list_of_vec (unit_vec n i)) J)"]
        by (smt (verit, best) A Collect_cong carrier_dim_vec carrier_matD(2) carrier_matI dim_submatrix(2) dim_vec fpfhpqwfcqw fwqfqwfojj mat_of_rows_carrier(3) nths_list_pick_vec_same unit_vec_carrier)
      
      then  have "row B (dim_row B - 1) = vec_of_list (nths (list_of_vec (unit_vec n i)) J)"
        using fpfhpqwfcqw 
        by (simp add: \<open>B = submatrix A I J @\<^sub>r mat_of_rows (card ({0..<n} \<inter> J)) [vec_of_list (nths (list_of_vec (unit_vec n i)) J)]\<close> append_rows_def)
      have 5:"vec_of_list (nths (list_of_vec (unit_vec n i)) J) =
          vec (card {ia. ia<dim_vec (unit_vec n i) \<and> ia\<in>J})  (\<lambda> ia. (unit_vec n i) $ (pick J ia))"
        using nths_list_pick_vec_same[of "(unit_vec n i)" J]
        by force
     then have 6:"\<forall> j < dim_col B. B $$ (dim_row B - 1,j) = (unit_vec n i) $ (pick J j)" 
          using 5 
          by (smt (verit, best) Matrix.row_def \<open>Matrix.row B (dim_row B - 1) = vec_of_list (nths (list_of_vec (unit_vec n i)) J)\<close> index_vec row_carrier vec_carrier_vec)
      
      show ?thesis
      proof(cases "i < n")
        case True
        have 7: "\<forall> j < dim_col B. pick J j \<noteq> i \<longrightarrow>  B $$ (dim_row B - 1,j) = 0"
        proof safe
          fix k
          assume asm: "k < dim_col B" "pick J k \<noteq> i"
          have "pick J k < n" 
            by (metis (no_types, lifting) "5" Collect_cong \<open>Matrix.row B (dim_row B - 1) = vec_of_list (nths (list_of_vec (unit_vec n i)) J)\<close> asm(1) index_unit_vec(3) pick_le row_carrier vec_carrier_vec)
          then have "(unit_vec n i) $ (pick J k) = 0" 
            unfolding unit_vec_def 
            
            using asm(2) by force
          then show " B $$ (dim_row B - 1, k) = 0" 
            using "6" asm(1) by auto
        qed
        have "\<forall> j < dim_col B. pick J j = i \<longrightarrow>  B $$ (dim_row B - 1,j) = 1"
          by (metis "6" True index_unit_vec(2))
      
         show ?thesis 
         proof(cases "\<exists>j. j < dim_col B \<and> pick J j = i")
           case True
           obtain j where j: "pick J j = i \<and> j < dim_col B" 
             using True by blast
           have "B $$ (dim_row B - 1,j) = 1" 
             using \<open>\<forall>j<dim_col B. pick J j = i \<longrightarrow> B $$ (dim_row B - 1, j) = 1\<close> \<open>pick J j = i \<and> j < dim_col B\<close> by presburger
           have "\<forall> k < dim_col B. k \<noteq> j \<longrightarrow>  B $$ (dim_row B - 1,k) = 0" 
           proof safe
             fix k
             assume asm: "k < dim_col B" " k \<noteq> j"
             have "pick J k \<noteq> i" 
             proof(rule ccontr)
               assume " \<not> pick J k \<noteq> i"
               then have "pick J k = pick J j" 
                 using j by fastforce
               show False
               proof(cases "infinite J")
                 case True
                 then show ?thesis 
                   using \<open>pick J k = pick J j\<close> asm(2) pick_eq_iff_inf by blast
               next
                 case False
                 have "dim_col B = (card {ia. ia<dim_col (A @\<^sub>r mat_of_rows n [unit_vec n i]) \<and> ia\<in>J})" 
                      using I_J dim_submatrix(2)
                      by blast
                    then have "dim_col B = (card {ia. ia<n \<and> ia\<in>J})" 
                      by (metis \<open>Matrix.row (A @\<^sub>r mat_of_rows n [unit_vec n i]) nr = unit_vec n i\<close> index_row(2) index_unit_vec(3))
                 have "j < card J" 
                   by (metis (mono_tags, lifting) \<open>dim_col B = card {ia. ia < n \<and> ia \<in> J}\<close> \<open>pick J k = pick J j\<close> asm(2) basic_trans_rules(21) card_mono j mem_Collect_eq not_less pick_eq_iff_inf subsetI)
                 then show ?thesis 
                   by (metis (mono_tags, lifting) False \<open>\<not> pick J k \<noteq> i\<close> \<open>dim_col B = card {ia. ia < n \<and> ia \<in> J}\<close> asm(1) asm(2) basic_trans_rules(21) card_mono j less_not_refl mem_Collect_eq nat_neq_iff not_less pick_mono subsetI)
               qed
             qed
             then show " B $$ (dim_row B - 1, k) = 0" 
               using "7" asm(1) by presburger
           qed
           have "\<forall>k \<in> {0..<dim_col B}. j\<noteq>k \<longrightarrow>  B $$ (dim_row B - 1,k) = 0" 
             using \<open>\<forall>k<dim_col B. k \<noteq> j \<longrightarrow> B $$ (dim_row B - 1, k) = 0\<close> atLeastLessThan_iff by blast
        
           then have "(\<Sum>j \<in> {0..<dim_col B}. B $$ (dim_row B - 1,j) * cofactor B (dim_row B - 1) j) =
               B $$ (dim_row B - 1,j) * cofactor B (dim_row B - 1) j" 
             using fhqwpfh[of "{0..<dim_col B}" j]
             by (metis (no_types, lifting) atLeast0LessThan finite_atLeastLessThan j lessThan_iff vector_space_over_itself.scale_eq_0_iff)
  
           then have "(\<Sum>j<dim_col B. B $$ (dim_row B - 1,j) * cofactor B (dim_row B - 1) j) =
              B $$ (dim_row B - 1,j) * cofactor B (dim_row B - 1) j" 
             by (metis atLeast0LessThan)
           then have "det B =  B $$ (dim_row B - 1,j) * cofactor B (dim_row B - 1) j"
             by (metis "4" \<open>dim_row B = dim_col B\<close>)
           then have "det B = cofactor B (dim_row B - 1) j" 
             using \<open>B $$ (dim_row B - 1, j) = 1\<close> l_one by presburger
           have 8: "cofactor B (dim_row B - 1) j = 
                (-1)^((dim_row B - 1)+j) * det (mat_delete B (dim_row B - 1) j)" 
             by (meson Determinant.cofactor_def)
           have 9:"mat_delete B (dim_row B - 1) j = submatrix A I (J - {pick J j})"
             using gbergre 
             by (smt (z3) "5" A Collect_cong One_nat_def Suc_eq_plus1 \<open>B = submatrix A I J @\<^sub>r submatrix (mat_of_rows n [unit_vec n i]) ((\<lambda>i. i - nr) ` (I - {0..<nr})) J\<close> \<open>Matrix.row B (dim_row B - 1) = vec_of_list (nths (list_of_vec (unit_vec n i)) J)\<close> \<open>submatrix (mat_of_rows n [unit_vec n i]) ((\<lambda>i. i - nr) ` (I - {0..<nr})) J = submatrix (mat_of_rows n [unit_vec n i]) {0} J\<close> append_rows_def carrier_matD(2) diff_add_inverse dim_submatrix(2) dim_vec fwqfqwfojj index_mat_four_block(2) index_row(2) index_unit_vec(3) index_zero_mat(2) j list.size(3) list.size(4) mat_of_rows_carrier(1) mat_of_rows_carrier(2) plus_1_eq_Suc unit_vec_carrier vec_carrier)
           have "det (submatrix A I (J - {pick J j})) \<in> {-1, 0, 1}" 
             using assms(2) unfolding tot_unimodular_def 
             by blast
           then have "cofactor B (dim_row B - 1) j \<in> {-1, 0, 1}" using 8 9 
             by (smt (z3) UNIV_I \<open>B $$ (dim_row B - 1, j) = 1\<close> \<open>Determinant.det B = B $$ (dim_row B - 1, j) * Determinant.cofactor B (dim_row B - 1) j\<close> \<open>Determinant.det B = Determinant.cofactor B (dim_row B - 1) j\<close> cring_simprules(11) cring_simprules(14) cring_simprules(24) insertCI insertE insert_absorb insert_iff insert_not_empty mult_minus1 nat_pow_distrib r_one square_eq_1_iff square_eq_one vector_space_over_itself.scale_eq_0_iff vector_space_over_itself.scale_left_imp_eq vector_space_over_itself.scale_right_imp_eq)
           then show ?thesis 
             using `det B = cofactor B (dim_row B - 1) j` by auto
         next
           case False
           then have "\<forall> j < dim_col B. B $$ (dim_row B - 1,j) = 0"
             using "7" by blast
           then have "det B = 0" 
             by (simp add: "4" \<open>dim_row B = dim_col B\<close>)
           then show ?thesis by auto
         qed
      next
        case False
        have "unit_vec n i = 0\<^sub>v n"
          unfolding unit_vec_def zero_vec_def 
          using False by fastforce
     then have "\<forall> j < dim_col B. B $$ (dim_row B - 1,j) = 0" 
       using 6
          by (metis (no_types, lifting) "5" Collect_cong \<open>Matrix.row B (dim_row B - 1) = vec_of_list (nths (list_of_vec (unit_vec n i)) J)\<close> \<open>unit_vec n i = 0\<^sub>v n\<close> carrier_vecD index_row(2) index_unit_vec(3) index_zero_vec(1) pick_le vec_carrier)
        then show ?thesis using 4 
          by (simp add: \<open>dim_row B = dim_col B\<close>)
      qed
    next
      case False
      have 3:"dim_row (mat_of_rows n [unit_vec n i]) =  1" using 1 
        by fast
      have "submatrix (mat_of_rows n [unit_vec n i]) (?f ` (I - {0..<nr})) J =
            submatrix (mat_of_rows n [unit_vec n i]) (?f ` (I - {0..<nr})\<inter>{0..<1}) J"
        using submatrix_inter_rows' 3 
        by metis
      have "?f ` (I - {0..<nr}) \<inter> {0..<1} = {}" 
        apply safe 
        apply simp+
        using False by auto
      
      have "submatrix (mat_of_rows n [unit_vec n i]) (?f ` (I - {0..<nr})) J = 
            submatrix (mat_of_rows n [unit_vec n i]) {} J" 
        by (metis \<open>(\<lambda>i. i - nr) ` (I - {0..<nr}) \<inter> {0..<1} = {}\<close> \<open>submatrix (mat_of_rows n [unit_vec n i]) ((\<lambda>i. i - nr) ` (I - {0..<nr})) J = submatrix (mat_of_rows n [unit_vec n i]) ((\<lambda>i. i - nr) ` (I - {0..<nr}) \<inter> {0..<1}) J\<close>)
      then have 11: "submatrix (mat_of_rows n [unit_vec n i]) {} J 
      = 0\<^sub>m 0 (dim_col (submatrix (mat_of_rows n [unit_vec n i]) (?f ` (I - {0..<nr})) J))"
        using bcqkcbpqw 
        by (smt (verit) Collect_cong dim_submatrix(2) mat_of_rows_carrier(3))
      have "B = submatrix A I J" 
        apply rule
          apply (metis "10" append_rows_def index_mat_four_block(1) trans_less_add1)
         apply (metis (no_types, lifting) "10" "11" \<open>submatrix (mat_of_rows n [unit_vec n i]) ((\<lambda>i. i - nr) ` (I - {0..<nr})) J = submatrix (mat_of_rows n [unit_vec n i]) {} J\<close> add.right_neutral append_rows_def index_mat_four_block(2) index_zero_mat(2))
        by (metis (no_types, lifting) A Collect_cong I_J \<open>Matrix.row (A @\<^sub>r mat_of_rows n [unit_vec n i]) nr = unit_vec n i\<close> carrier_matD(2) dim_submatrix(2) index_row(2) index_unit_vec(3))
      then show ?thesis
        using assms(2) unfolding tot_unimodular_def by auto
    qed
  qed
qed
qed

lemma dnwqofihq:

shows "- unit_vec n i = vec n (\<lambda> j. if j = i then - 1 else (0::'a))"
  unfolding uminus_vec_def unit_vec_def
  by force

lemma uminus_zero_vec:
  shows "(0\<^sub>v n :: 'a vec) = - 0\<^sub>v n" 
  unfolding zero_vec_def 
proof
  show "dim_vec (Matrix.vec n (\<lambda>i. 0)) = dim_vec (- Matrix.vec n (\<lambda>i. 0))" by simp
  fix i
  assume "i  < dim_vec (- Matrix.vec n (\<lambda>i. 0))"
  show " Matrix.vec n (\<lambda>i. 0 :: 'a) $v i = (- Matrix.vec n (\<lambda>i. 0)) $v i"
  using \<open>i < dim_vec (- Matrix.vec n (\<lambda>i. 0))\<close> by auto
qed

lemma uminus_vec_if_zero:
  assumes "v \<in> carrier_vec n"
  assumes "v = (0\<^sub>v n :: 'a vec)"
  shows "-v = 0\<^sub>v n"
  using uminus_zero_vec assms 
  by argo
  

lemma tot_unimod_append_minus_unit_vec:
 fixes A :: "'a  mat"
   assumes A: "A \<in> carrier_mat nr n" 
   assumes "tot_unimodular A"
   shows "tot_unimodular (A @\<^sub>r mat_of_rows n [(- (unit_vec n i):: 'a vec)])" (is "tot_unimodular ?A'")
  unfolding tot_unimodular_def
proof rule
  fix B
  show " (\<exists>I J. submatrix (A @\<^sub>r mat_of_rows n [(- (unit_vec n i) :: 'a vec)])I J = B) \<longrightarrow> det B \<in> {- 1, 0, 1}" 
  proof
  assume asm:"\<exists>I J. submatrix (A @\<^sub>r mat_of_rows n [(- (unit_vec n i) :: 'a vec)]) I J = B"
  then show "det B \<in> {-1,0,1}" 
  proof(cases "dim_row B \<noteq> dim_col B")
    case True
    then show ?thesis unfolding Determinant.det_def 
      by (meson insertCI)
  next
    case False
    then  have "dim_row B = dim_col B" by auto
    obtain I J where I_J: "submatrix (A @\<^sub>r mat_of_rows n [(- (unit_vec n i) :: 'a vec)]) I J = B"
      using asm by presburger
    have 1: "mat_of_rows n [(- (unit_vec n i) :: 'a vec)] \<in> carrier_mat 1 n" 
      using mat_of_rows_carrier(1)[of n "[unit_vec n i]"] 
      by auto
    have "row ?A' nr = (- (unit_vec n i) :: 'a vec)" 
      using append_rows_nth(2)[OF A 1] mat_of_rows_row by simp 
    have 2: "B \<in> carrier_mat (dim_row B) (dim_row B)" 
      by (metis False carrier_matI)
    let ?f = "(\<lambda> i. i - nr)"

    have 10:"B = submatrix A I J @\<^sub>r submatrix (mat_of_rows n [(- (unit_vec n i) :: 'a vec)]) (?f ` (I - {0..<nr})) J"
      using fcdnwe[OF A 1]
      using I_J by blast


    show ?thesis 
    proof(cases "nr \<in> I")
      case True
      have "{ia. ia < dim_row (A @\<^sub>r mat_of_rows n [(- (unit_vec n i) :: 'a vec)]) \<and> ia \<in> I} \<noteq> {}"
        by (smt (verit, del_insts) Collect_empty_eq True add.right_neutral add_Suc_right 
            append_rows_def assms(1) carrier_matD(1) index_mat_four_block(2) index_zero_mat(2)
            lessI list.size(3) list.size(4) mat_of_rows_carrier(2))
      have "finite {ia. ia < dim_row (A @\<^sub>r mat_of_rows n [(- (unit_vec n i) :: 'a vec)]) \<and> ia \<in> I}"
        using finite_nat_set_iff_bounded by blast
      then have "card {ia. ia < dim_row (A @\<^sub>r mat_of_rows n [(- (unit_vec n i) :: 'a vec)]) \<and> ia \<in> I} > 0"
        using \<open>{ia. ia < dim_row (A @\<^sub>r mat_of_rows n [(- (unit_vec n i) :: 'a vec)]) \<and> ia \<in> I} \<noteq> {}\<close> card_gt_0_iff by blast
      then have "dim_row (submatrix ?A' I J) > 0" 
          using dim_submatrix(1)[of ?A' I J]  
          by linarith
      then have "dim_row B - 1 < dim_row B" 
        using I_J diff_less verit_comp_simplify(28) by blast
      have 4: "det B = (\<Sum>j<dim_row B. B $$ (dim_row B - 1,j) * cofactor B (dim_row B - 1) j)"
        using laplace_expansion_row[OF 2] 
        using \<open>dim_row B - 1 < dim_row B\<close> by blast
      have 3:"dim_row (mat_of_rows n [(- (unit_vec n i) :: 'a vec)]) =  1" using 1 
        by fast
      have "submatrix (mat_of_rows n [(- (unit_vec n i) :: 'a vec)]) (?f ` (I - {0..<nr})) J =
            submatrix (mat_of_rows n [(- (unit_vec n i) :: 'a vec)]) (?f ` (I - {0..<nr})\<inter>{0..<1}) J"
        using submatrix_inter_rows' 3 
        by metis
      have "?f ` (I - {0..<nr}) \<inter> {0..<1} = {0}" 
        apply safe 
          apply simp+
         apply (metis DiffI True atLeastLessThan_iff diff_self_eq_0 image_iff less_irrefl)
        by simp
      have "submatrix (mat_of_rows n [(- (unit_vec n i) :: 'a vec)]) (?f ` (I - {0..<nr})) J =
          submatrix (mat_of_rows n [(- (unit_vec n i) :: 'a vec)]) {0} J" 
        by (metis \<open>(\<lambda>i. i - nr) ` (I - {0..<nr}) \<inter> {0..<1} = {0}\<close>
            \<open>submatrix (mat_of_rows n [(- (unit_vec n i) :: 'a vec)]) ((\<lambda>i. i - nr) ` (I - {0..<nr})) J = submatrix (mat_of_rows n [(- (unit_vec n i) :: 'a vec)]) ((\<lambda>i. i - nr) ` (I - {0..<nr}) \<inter> {0..<1}) J\<close>)
      have "B = submatrix A I J @\<^sub>r submatrix (mat_of_rows n [(- (unit_vec n i) :: 'a vec)]) {0} J" 
        by (simp add: \<open>B = submatrix A I J @\<^sub>r submatrix (mat_of_rows n [(- (unit_vec n i) :: 'a vec)]) ((\<lambda>i. i - nr) ` (I - {0..<nr})) J\<close>
            \<open>submatrix (mat_of_rows n [(- (unit_vec n i) :: 'a vec)]) ((\<lambda>i. i - nr) ` (I - {0..<nr})) J = submatrix (mat_of_rows n [(- (unit_vec n i) :: 'a vec)]) {0} J\<close>)
      have "B = submatrix A I J @\<^sub>r mat_of_rows (card ({0..<n} \<inter> J)) [vec_of_list (nths (list_of_vec ((- (unit_vec n i) :: 'a vec))) J)]"
        by (simp add: \<open>B = submatrix A I J @\<^sub>r submatrix (mat_of_rows n [(- (unit_vec n i) :: 'a vec)]) {0} J\<close> fwqfqwfojj)
      have 12:"(- (unit_vec n i) :: 'a vec) \<in> carrier_vec n" 
        using uminus_carrier_vec unit_vec_carrier by blast
        then  have "row (submatrix A I J @\<^sub>r mat_of_rows (card ({0..<n} \<inter> J)) [vec_of_list (nths (list_of_vec ((- (unit_vec n i) :: 'a vec))) J)]) 
        (dim_row (submatrix A I J)) = vec_of_list (nths (list_of_vec ((- (unit_vec n i) :: 'a vec))) J)"
        using fpfhpqwfcqw[of "submatrix A I J" "card ({0..<nr} \<inter> I)" "card ({0..<n} \<inter> J)" "vec_of_list (nths (list_of_vec ((- (unit_vec n i) :: 'a vec))) J)"]
       A Collect_cong carrier_dim_vec carrier_matD(2) carrier_matI dim_submatrix(2) dim_vec fpfhpqwfcqw fwqfqwfojj mat_of_rows_carrier(3) nths_list_pick_vec_same unit_vec_carrier
        by (smt (verit, best)) 
        
      
      then  have "row B (dim_row B - 1) = vec_of_list (nths (list_of_vec ((- (unit_vec n i) :: 'a vec))) J)"
        using fpfhpqwfcqw 
        by (simp add: \<open>B = submatrix A I J @\<^sub>r mat_of_rows (card ({0..<n} \<inter> J)) [vec_of_list (nths (list_of_vec ((- (unit_vec n i) :: 'a vec))) J)]\<close> append_rows_def)
      have 5:"vec_of_list (nths (list_of_vec ((- (unit_vec n i) :: 'a vec))) J) =
          vec (card {ia. ia<dim_vec ((- (unit_vec n i) :: 'a vec)) \<and> ia\<in>J})  (\<lambda> ia. ((- (unit_vec n i) :: 'a vec)) $ (pick J ia))"
        using nths_list_pick_vec_same[of "((- (unit_vec n i) :: 'a vec))" J]
        by force
     then have 6:"\<forall> j < dim_col B. B $$ (dim_row B - 1,j) = ((- (unit_vec n i) :: 'a vec)) $ (pick J j)" 
          using 5 
          by (smt (verit, best) Matrix.row_def \<open>Matrix.row B (dim_row B - 1) = vec_of_list (nths (list_of_vec ((- (unit_vec n i) :: 'a vec))) J)\<close> index_vec row_carrier vec_carrier_vec)
      
      show ?thesis
      proof(cases "i < n")
        case True
        have 7: "\<forall> j < dim_col B. pick J j \<noteq> i \<longrightarrow>  B $$ (dim_row B - 1,j) = 0"
        proof safe
          fix k
          assume asm: "k < dim_col B" "pick J k \<noteq> i"
          have "pick J k < n" using 12 
            "5" Collect_cong \<open>Matrix.row B (dim_row B - 1) = vec_of_list (nths (list_of_vec ((- (unit_vec n i) :: 'a vec))) J)\<close> asm(1)  pick_le row_carrier vec_carrier_vec 
            by (metis (no_types, lifting) carrier_vecD)
          have 8:"- Matrix.vec n (\<lambda>j. if j = i then 1 else (0::'a)) = 
           Matrix.vec n (\<lambda>j. if j = i then - 1 else (0::'a))"
          proof rule
            show "dim_vec (- Matrix.vec n (\<lambda>j. if j = i then 1 else (0::'a))) =
    dim_vec (Matrix.vec n (\<lambda>j. if j = i then - 1 else (0::'a)))" by simp
            fix ia
            assume "ia < dim_vec (Matrix.vec n (\<lambda>j. if j = i then - 1 else (0::'a)))"
            show " (- Matrix.vec n (\<lambda>j. if j = i then 1 else (0::'a))) $v ia =
          Matrix.vec n (\<lambda>j. if j = i then - 1 else (0::'a)) $v ia"
            proof(cases "ia = i")
              case True
              then show ?thesis 
                using \<open>ia < dim_vec (Matrix.vec n (\<lambda>j. if j = i then - 1 else 0))\<close> by auto
            next
              case False
              have " (- Matrix.vec n (\<lambda>j. if j = i then 1 else (0::'a))) $v ia = - (0::'a)"
                using False \<open>ia < dim_vec (Matrix.vec n (\<lambda>j. if j = i then - 1 else 0))\<close> by force
              have "(Matrix.vec n (\<lambda>j. if j = i then - 1 else (0::'a))) $v ia = (0::'a)"
                using False \<open>ia < dim_vec (Matrix.vec n (\<lambda>j. if j = i then - 1 else 0))\<close> by auto
              have  "(0::'a) = - 0" 
                by simp
              then show ?thesis  
                using \<open>(- Matrix.vec n (\<lambda>j. if j = i then 1 else 0)) $v ia = - 0\<close> \<open>Matrix.vec n (\<lambda>j. if j = i then - 1 else 0) $v ia = 0\<close> by presburger
            qed
          qed
           
          
          have "((- (unit_vec n i) :: 'a vec)) $ (pick J k) = 0"
            unfolding uminus_vec_def unit_vec_def using 8 
            by (simp add: \<open>pick J k < n\<close> asm(2))
            
          then show " B $$ (dim_row B - 1, k) = 0" 
            using "6" asm(1) by auto
        qed
        have "\<forall> j < dim_col B. pick J j = i \<longrightarrow>  B $$ (dim_row B - 1,j) = ( - 1 :: 'a)"
          using "6" True by auto
      
         show ?thesis 
         proof(cases "\<exists>j. j < dim_col B \<and> pick J j = i")
           case True
           obtain j where j: "pick J j = i \<and> j < dim_col B" 
             using True by blast
           have "B $$ (dim_row B - 1,j) = - 1" 
             using \<open>\<forall>j<dim_col B. pick J j = i \<longrightarrow> B $$ (dim_row B - 1, j) = - 1\<close> \<open>pick J j = i \<and> j < dim_col B\<close> by presburger
           have "\<forall> k < dim_col B. k \<noteq> j \<longrightarrow>  B $$ (dim_row B - 1,k) = 0" 
           proof safe
             fix k
             assume asm: "k < dim_col B" " k \<noteq> j"
             have "pick J k \<noteq> i" 
             proof(rule ccontr)
               assume " \<not> pick J k \<noteq> i"
               then have "pick J k = pick J j" 
                 using j by fastforce
               show False
               proof(cases "infinite J")
                 case True
                 then show ?thesis 
                   using \<open>pick J k = pick J j\<close> asm(2) pick_eq_iff_inf by blast
               next
                 case False
                 have "dim_col B = (card {ia. ia<dim_col (A @\<^sub>r mat_of_rows n [- unit_vec n i]) \<and> ia\<in>J})" 
                      using I_J dim_submatrix(2)
                      by blast
                    then have "dim_col B = (card {ia. ia<n \<and> ia\<in>J})" 
                      by (metis "12" Collect_cong \<open>Matrix.row (A @\<^sub>r mat_of_rows n [- unit_vec n i]) nr = - unit_vec n i\<close> carrier_vecD index_row(2))
                 have "j < card J" 
                   by (metis (mono_tags, lifting) \<open>dim_col B = card {ia. ia < n \<and> ia \<in> J}\<close> \<open>pick J k = pick J j\<close> asm(2) basic_trans_rules(21) card_mono j mem_Collect_eq not_less pick_eq_iff_inf subsetI)
                 then show ?thesis 
                   by (metis (mono_tags, lifting) False \<open>\<not> pick J k \<noteq> i\<close> \<open>dim_col B = card {ia. ia < n \<and> ia \<in> J}\<close> asm(1) asm(2) basic_trans_rules(21) card_mono j less_not_refl mem_Collect_eq nat_neq_iff not_less pick_mono subsetI)
               qed
             qed
             then show " B $$ (dim_row B - 1, k) = 0" 
               using "7" asm(1) by presburger
           qed
           have "\<forall>k \<in> {0..<dim_col B}. j\<noteq>k \<longrightarrow>  B $$ (dim_row B - 1,k) = 0" 
             using \<open>\<forall>k<dim_col B. k \<noteq> j \<longrightarrow> B $$ (dim_row B - 1, k) = 0\<close> atLeastLessThan_iff by blast
        
           then have "(\<Sum>j \<in> {0..<dim_col B}. B $$ (dim_row B - 1,j) * cofactor B (dim_row B - 1) j) =
               B $$ (dim_row B - 1,j) * cofactor B (dim_row B - 1) j" 
             using fhqwpfh[of "{0..<dim_col B}" j]
             by (metis (no_types, lifting) atLeast0LessThan finite_atLeastLessThan j lessThan_iff vector_space_over_itself.scale_eq_0_iff)
  
           then have "(\<Sum>j<dim_col B. B $$ (dim_row B - 1,j) * cofactor B (dim_row B - 1) j) =
              B $$ (dim_row B - 1,j) * cofactor B (dim_row B - 1) j" 
             by (metis atLeast0LessThan)
           then have "det B =  B $$ (dim_row B - 1,j) * cofactor B (dim_row B - 1) j"
             by (metis "4" \<open>dim_row B = dim_col B\<close>)
           then have "det B = - cofactor B (dim_row B - 1) j" 
             by (metis \<open>B $$ (dim_row B - 1, j) = - 1\<close> mult_minus1)

           have 8: "cofactor B (dim_row B - 1) j = 
                (-1)^((dim_row B - 1)+j) * det (mat_delete B (dim_row B - 1) j)" 
             by (meson Determinant.cofactor_def)
           have " - unit_vec n i \<in> carrier_vec n" 
             by simp
           then have "vec_of_list (nths (list_of_vec (- unit_vec n i)) J) \<in> carrier_vec (dim_col (submatrix A I J))"
             by (smt (verit) A Collect_cong carrier_dim_vec carrier_matD(2) dim_submatrix(2) dim_vec nths_list_pick_vec_same)
          
           then have 9:"mat_delete B (dim_row B - 1) j = submatrix A I (J - {pick J j})"
             using gbergre[of A nr "vec_of_list (nths (list_of_vec (- unit_vec n i)) J)" "submatrix A I J" I J j] \<open>B = submatrix A I J @\<^sub>r submatrix (mat_of_rows n [- unit_vec n i]) ((\<lambda>i. i - nr) ` (I - {0..<nr})) J\<close>
\<open>Matrix.row B (dim_row B - 1) = vec_of_list (nths (list_of_vec (- unit_vec n i)) J)\<close> \<open>submatrix (mat_of_rows n [- unit_vec n i]) ((\<lambda>i. i - nr) ` (I - {0..<nr})) J = submatrix (mat_of_rows n [- unit_vec n i]) {0} J\<close>
             by (smt (verit, best) "12" "5" Collect_cong assms(1) carrier_vecD dim_submatrix(1) dim_submatrix(2) fwqfqwfojj index_row(2) j mat_delete_dim(1) mat_of_rows_carrier(3) vec_carrier_vec)
            have "det (submatrix A I (J - {pick J j})) \<in> {-1, 0, 1}" 
             using assms(2) unfolding tot_unimodular_def 
             by blast
           then have "cofactor B (dim_row B - 1) j \<in> {-1, 0, 1}" using 8 9 
             by (smt (z3) UNIV_I \<open>B $$ (dim_row B - 1, j) = -1\<close> \<open>Determinant.det B = B $$ (dim_row B - 1, j) * Determinant.cofactor B (dim_row B - 1) j\<close> \<open>Determinant.det B = - Determinant.cofactor B (dim_row B - 1) j\<close> cring_simprules(11) cring_simprules(14) cring_simprules(24) insertCI insertE insert_absorb insert_iff insert_not_empty mult_minus1 nat_pow_distrib r_one square_eq_1_iff square_eq_one vector_space_over_itself.scale_eq_0_iff vector_space_over_itself.scale_left_imp_eq vector_space_over_itself.scale_right_imp_eq)
           then show ?thesis 
             using `det B = - cofactor B (dim_row B - 1) j` by auto
         next
           case False
           then have "\<forall> j < dim_col B. B $$ (dim_row B - 1,j) = 0"
             using "7" by blast
           then have "det B = 0" 
             by (simp add: "4" \<open>dim_row B = dim_col B\<close>)
           then show ?thesis by auto
         qed
      next
        case False
        have 13:"unit_vec n i \<in> carrier_vec n" 
          by simp
        have 14:"unit_vec n i = 0\<^sub>v n" 
          unfolding unit_vec_def  zero_vec_def 
          using False by fastforce
        have "((- unit_vec n i) :: 'a vec) = 0\<^sub>v n"
          using uminus_vec_if_zero[OF 13 14] 
          by simp
     then have "\<forall> j < dim_col B. B $$ (dim_row B - 1,j) = 0" 
       using 6
 "5" Collect_cong \<open>Matrix.row B (dim_row B - 1) = vec_of_list (nths (list_of_vec (- unit_vec n i)) J)\<close> \<open>- unit_vec n i = 0\<^sub>v n\<close> carrier_vecD index_row(2)  index_zero_vec(1) pick_le vec_carrier
       by (metis (no_types, lifting) dnwqofihq)
         then show ?thesis using 4 
          by (simp add: \<open>dim_row B = dim_col B\<close>)
      qed
    next
      case False
      have 3:"dim_row (mat_of_rows n [(- unit_vec n i):: 'a vec]) =  1" using 1 
        by fast
      have "submatrix (mat_of_rows n [(- unit_vec n i):: 'a vec]) (?f ` (I - {0..<nr})) J =
            submatrix (mat_of_rows n [(- unit_vec n i):: 'a vec]) (?f ` (I - {0..<nr})\<inter>{0..<1}) J"
        using submatrix_inter_rows' 3 
        by metis
      have "?f ` (I - {0..<nr}) \<inter> {0..<1} = {}" 
        apply safe 
        apply simp+
        using False by auto
      
      have "submatrix (mat_of_rows n [(- unit_vec n i):: 'a vec]) (?f ` (I - {0..<nr})) J = 
            submatrix (mat_of_rows n [- unit_vec n i]) {} J" 
        by (metis \<open>(\<lambda>i. i - nr) ` (I - {0..<nr}) \<inter> {0..<1} = {}\<close> \<open>submatrix (mat_of_rows n [- unit_vec n i]) ((\<lambda>i. i - nr) ` (I - {0..<nr})) J = submatrix (mat_of_rows n [- unit_vec n i]) ((\<lambda>i. i - nr) ` (I - {0..<nr}) \<inter> {0..<1}) J\<close>)
      then have 11: "submatrix (mat_of_rows n [- unit_vec n i]) {} J 
      = 0\<^sub>m 0 (dim_col (submatrix (mat_of_rows n [- unit_vec n i]) (?f ` (I - {0..<nr})) J))"
        using bcqkcbpqw 
        by (smt (verit) Collect_cong dim_submatrix(2) mat_of_rows_carrier(3))
      have "B = submatrix A I J" 
        apply rule
          apply (metis "10" append_rows_def index_mat_four_block(1) trans_less_add1)
         apply (metis (no_types, lifting) "10" "11" \<open>submatrix (mat_of_rows n [- unit_vec n i]) ((\<lambda>i. i - nr) ` (I - {0..<nr})) J = submatrix (mat_of_rows n [- unit_vec n i]) {} J\<close> add.right_neutral append_rows_def index_mat_four_block(2) index_zero_mat(2))
       
         using A  I_J \<open>Matrix.row (A @\<^sub>r mat_of_rows n [- unit_vec n i]) nr = - unit_vec n i\<close> carrier_matD(2) dim_submatrix(2) index_row(2) index_unit_vec(3)
        by (metis (mono_tags) index_uminus_vec(2))
         then show ?thesis
        using assms(2) unfolding tot_unimodular_def by auto
    qed
  qed
qed
qed

lemma pweqfh:
   fixes A :: "'a  mat"
   assumes A: "A \<in> carrier_mat nr n"
   shows "submatrix A {0..<nr-1} UNIV \<in> carrier_mat (nr-1) n"
proof
  show "dim_row (submatrix A {0..<nr - 1} UNIV) = nr - 1" 
  proof -
    have "dim_row (submatrix A {0..<nr-1} UNIV) = card {i. i<dim_row A \<and> i\<in>{0..<nr-1}}" 
      using dim_submatrix(1) by blast
    have "{i. i<dim_row A \<and> i\<in>{0..<nr-1}} = {i. i<nr \<and> i\<in>{0..<nr-1}}" 
      using A by blast
    have "{i. i<nr \<and> i\<in>{0..<nr-1}} = {0..<nr-1}" 
      apply safe
      by simp
    then show ?thesis 
      using \<open>dim_row (submatrix A {0..<nr - 1} UNIV) = card {i. i < dim_row A \<and> i \<in> {0..<nr - 1}}\<close> \<open>{i. i < dim_row A \<and> i \<in> {0..<nr - 1}} = {i. i < nr \<and> i \<in> {0..<nr - 1}}\<close> card_atLeastLessThan minus_nat.diff_0 by presburger
  qed
  show "dim_col (submatrix A {0..<nr - 1} UNIV) = n" 
    using A dim_col_submatrix_UNIV by blast
qed

lemma cnoewqfqf:
  fixes A :: "'a  mat"
  assumes A: "A \<in> carrier_mat nr n"
  assumes "nr > 0"
  shows "A = (submatrix A {0..<nr-1} UNIV) @\<^sub>r (mat_of_rows n [row A (nr-1)])"
proof 
  have "  dim_row
     (submatrix A {0..<nr - 1} UNIV @\<^sub>r mat_of_rows n [Matrix.row A (nr - 1)]) = nr" 
    using pweqfh 
    by (metis (no_types, lifting) One_nat_def Suc_eq_plus1 append_rows_def assms(1) assms(2) carrier_matD(1) discrete index_mat_four_block(2) index_zero_mat(2) le_add_diff_inverse2 list.size(3) list.size(4) mat_of_rows_carrier(2))
  then show "dim_row A = dim_row (submatrix A {0..<nr - 1} UNIV @\<^sub>r mat_of_rows n [Matrix.row A (nr - 1)])"
    by (metis assms(1) carrier_matD(1))
  show "dim_col A = dim_col (submatrix A {0..<nr - 1} UNIV @\<^sub>r mat_of_rows n [Matrix.row A (nr - 1)])" 
    by (metis assms(1) carrier_matD(2) fpfhpqwfcqw index_row(2) pweqfh row_carrier)
  fix i j
  assume asmi: "i < dim_row (submatrix A {0..<nr - 1} UNIV @\<^sub>r mat_of_rows n [Matrix.row A (nr - 1)])"
  assume asmj: "j < dim_col (submatrix A {0..<nr - 1} UNIV @\<^sub>r mat_of_rows n [Matrix.row A (nr - 1)])"
  show "A $$ (i, j) = (submatrix A {0..<nr - 1} UNIV @\<^sub>r mat_of_rows n [Matrix.row A (nr - 1)]) $$ (i, j)"
  proof(cases "i < nr-1")
    case True
    have "row (submatrix A {0..<nr - 1} UNIV @\<^sub>r mat_of_rows n [Matrix.row A (nr - 1)]) i = 
          row (submatrix A {0..<nr - 1} UNIV) i" 
      by (meson Missing_Matrix.append_rows_nth(1) True assms(1) mat_of_rows_carrier(1) pweqfh)
    have "row (submatrix A {0..<nr - 1} UNIV) i = row A (pick  {0..<nr - 1} i)"
 using row_submatrix_UNIV[of i A "{0..<nr - 1}"]
  by (metis (no_types, lifting) A True carrier_matD(1) dim_submatrix(1) pweqfh row_submatrix_UNIV)
  have "i \<in> {0..<nr - 1}" using True 
    by simp
  then have "pick {0..<nr - 1} (card {a \<in> {0..<nr - 1}. a < i}) = i" 
    using pick_card_in_set by presburger
  have "{a \<in> {0..<nr - 1}. a < i} = {0..< i}"
    apply safe 
    using atLeastLessThan_iff apply blast
    using True by auto+
  then have "card {a \<in> {0..<nr - 1}. a < i} = i" 
    by force
  have "(pick  {0..<nr - 1} i) = i" 
    using \<open>card {a \<in> {0..<nr - 1}. a < i} = i\<close> \<open>pick {0..<nr - 1} (card {a \<in> {0..<nr - 1}. a < i}) = i\<close> by presburger
  then have "row A i = row (submatrix A {0..<nr - 1} UNIV) i" 
  using \<open>Matrix.row (submatrix A {0..<nr - 1} UNIV) i = Matrix.row A (pick {0..<nr - 1} i)\<close> by presburger
    then show ?thesis 
      by (metis \<open>Matrix.row (submatrix A {0..<nr - 1} UNIV @\<^sub>r mat_of_rows n [Matrix.row A (nr - 1)]) i = Matrix.row (submatrix A {0..<nr - 1} UNIV) i\<close> \<open>dim_col A = dim_col (submatrix A {0..<nr - 1} UNIV @\<^sub>r mat_of_rows n [Matrix.row A (nr - 1)])\<close> \<open>dim_row A = dim_row (submatrix A {0..<nr - 1} UNIV @\<^sub>r mat_of_rows n [Matrix.row A (nr - 1)])\<close> asmi asmj index_row(1))
  next
    case False
    have "i = nr - 1" 
      using False \<open>dim_row (submatrix A {0..<nr - 1} UNIV @\<^sub>r mat_of_rows n [Matrix.row A (nr - 1)]) = nr\<close> asmi by linarith
    then show ?thesis 
      by (metis \<open>dim_col A = dim_col (submatrix A {0..<nr - 1} UNIV @\<^sub>r mat_of_rows n [Matrix.row A (nr - 1)])\<close> \<open>dim_row A = dim_row (submatrix A {0..<nr - 1} UNIV @\<^sub>r mat_of_rows n [Matrix.row A (nr - 1)])\<close> asmi asmj assms(1) carrier_matD(2) fpfhpqwfcqw index_row(1) pweqfh row_carrier)
  qed
qed

lemma ngwpegp:
 fixes A :: "'a  mat"
 assumes A: "A \<in> carrier_mat nr1 n" 
 assumes B: "B \<in> carrier_mat nr2 n"
 assumes C: "C \<in> carrier_mat nr3 n"
 shows "A @\<^sub>r (B @\<^sub>r C) = (A @\<^sub>r B) @\<^sub>r C" 
proof
  show "dim_row (A @\<^sub>r B @\<^sub>r C) = dim_row ((A @\<^sub>r B) @\<^sub>r C)" 
    by (simp add: append_rows_def)
  show "dim_col (A @\<^sub>r B @\<^sub>r C) = dim_col ((A @\<^sub>r B) @\<^sub>r C)" 
    by (smt (verit, ccfv_SIG) C assms(1) assms(2) carrier_append_rows carrier_matD(2))
  fix i j
  assume asmi: "i < dim_row ((A @\<^sub>r B) @\<^sub>r C)"
  assume asmj: "j < dim_col ((A @\<^sub>r B) @\<^sub>r C)"
  show "(A @\<^sub>r B @\<^sub>r C) $$ (i, j) = ((A @\<^sub>r B) @\<^sub>r C) $$ (i, j)" 
  proof(cases "i < nr1 + nr2")
    case True
    have "row ((A @\<^sub>r B) @\<^sub>r C) i = row (A @\<^sub>r B) i" 
      by (meson Missing_Matrix.append_rows_nth(1) True assms(1) assms(2) assms(3) carrier_append_rows)
    show ?thesis 
    proof(cases "i < nr1")
      case True
      have "row (A @\<^sub>r B @\<^sub>r C) i = row A i" 
        by (metis True append_rows_index_same assms(1) assms(2) assms(3) carrier_append_rows carrier_matD(1))
      have "row (A @\<^sub>r B) i = row A i" 
        using Missing_Matrix.append_rows_nth(1) True assms(1) assms(2) by blast
      then show ?thesis 
        by (metis \<open>Matrix.row ((A @\<^sub>r B) @\<^sub>r C) i = Matrix.row (A @\<^sub>r B) i\<close> \<open>Matrix.row (A @\<^sub>r B @\<^sub>r C) i = Matrix.row A i\<close> \<open>dim_col (A @\<^sub>r B @\<^sub>r C) = dim_col ((A @\<^sub>r B) @\<^sub>r C)\<close> \<open>dim_row (A @\<^sub>r B @\<^sub>r C) = dim_row ((A @\<^sub>r B) @\<^sub>r C)\<close> asmi asmj index_row(1))
    next
      case False
      have "row (A @\<^sub>r B) i = row B (i - nr1)" 
        by (meson B False True assms(1) gram_schmidt.append_rows_index_same' not_le)
      have "row (A @\<^sub>r B @\<^sub>r C) i = row (B @\<^sub>r C) (i - nr1)" 
        by (smt (verit, ccfv_SIG) B C False \<open>dim_row (A @\<^sub>r B @\<^sub>r C) = dim_row ((A @\<^sub>r B) @\<^sub>r C)\<close> add_diff_inverse_nat append_rows_def append_rows_index_same append_rows_index_same' asmi assms(1) carrier_matD(1) carrier_matD(2) carrier_matI index_mat_four_block(2) index_row(2) index_zero_mat(2) nat_add_left_cancel_less not_less)

      then show ?thesis 
        by (metis (no_types, lifting) B C False True \<open>Matrix.row ((A @\<^sub>r B) @\<^sub>r C) i = Matrix.row (A @\<^sub>r B) i\<close> \<open>Matrix.row (A @\<^sub>r B) i = Matrix.row B (i - nr1)\<close> \<open>dim_col (A @\<^sub>r B @\<^sub>r C) = dim_col ((A @\<^sub>r B) @\<^sub>r C)\<close> \<open>dim_row (A @\<^sub>r B @\<^sub>r C) = dim_row ((A @\<^sub>r B) @\<^sub>r C)\<close> add_diff_inverse_nat append_rows_index_same asmi asmj carrier_matD(1) index_row(1) nat_add_left_cancel_less)
    qed
  next
    case False
    have "i \<ge> nr1" 
      using False by linarith
    have "B @\<^sub>r C \<in> carrier_mat (nr2 + nr3) n" 
      using assms(2) assms(3) by blast
    have "i < nr1 + nr2 + nr3" 
      by (metis append_rows_def asmi assms(1) assms(2) assms(3) carrier_matD(1) index_mat_four_block(2) index_zero_mat(2))
    have "row (A @\<^sub>r B @\<^sub>r C) i = row (B @\<^sub>r C) (i - nr1)" 
      using append_rows_nth(2)[of A nr1 n "B @\<^sub>r C" "nr2+nr3" i]
      by (metis Groups.add_ac(1) \<open>B @\<^sub>r C \<in> carrier_mat (nr2 + nr3) n\<close> \<open>i < nr1 + nr2 + nr3\<close> \<open>nr1 \<le> i\<close>  assms(1))
    have 1:"i - nr1 \<ge> nr2" 
      using False by linarith
    have "row (B @\<^sub>r C) (i - nr1) = row C (i - (nr1+nr2))" 
      using append_rows_nth(2)[OF B C 1] 
      by (metis \<open>i < nr1 + nr2 + nr3\<close> \<open>nr1 \<le> i\<close> add.assoc add.commute diff_diff_eq less_diff_conv2)
    have "row ((A @\<^sub>r B) @\<^sub>r C) i = row C (i - (nr1+nr2))"
      using append_rows_nth(2)[of "A @\<^sub>r B" "nr1+nr2" n C nr3 i] 
      by (meson False \<open>i < nr1 + nr2 + nr3\<close> assms(1) assms(2) assms(3) carrier_append_rows leI)
    then show ?thesis 
      by (metis \<open>Matrix.row (A @\<^sub>r B @\<^sub>r C) i = Matrix.row (B @\<^sub>r C) (i - nr1)\<close> \<open>Matrix.row (B @\<^sub>r C) (i - nr1) = Matrix.row C (i - (nr1 + nr2))\<close> \<open>dim_col (A @\<^sub>r B @\<^sub>r C) = dim_col ((A @\<^sub>r B) @\<^sub>r C)\<close> \<open>dim_row (A @\<^sub>r B @\<^sub>r C) = dim_row ((A @\<^sub>r B) @\<^sub>r C)\<close> asmi asmj index_row(1))
  qed
qed

lemma append_mat_empty:
   fixes A :: "'a  mat"
  assumes A: "A \<in> carrier_mat nr n"
  assumes B: "B \<in> carrier_mat 0 n"
  shows "A @\<^sub>r B = A" 
proof
  show "dim_row (A @\<^sub>r B) = dim_row A" 
    by (metis add_cancel_right_right append_rows_def assms(2) carrier_matD(1) index_mat_four_block(2) index_zero_mat(2))
  show "dim_col (A @\<^sub>r B) = dim_col A" 
    using assms(1) assms(2) carrier_matD(2) by blast
  fix i j
  assume asmi: "i < dim_row A" 
  assume asmj: "j < dim_col A" 
  show "(A @\<^sub>r B) $$ (i, j) = A $$ (i, j)" 
  proof(cases "i < nr")
    case True
    have "row (A @\<^sub>r B) i = row A i" 
      using Missing_Matrix.append_rows_nth(1) True assms(1) assms(2) by blast
    then show ?thesis 
      by (metis \<open>dim_col (A @\<^sub>r B) = dim_col A\<close> \<open>dim_row (A @\<^sub>r B) = dim_row A\<close> asmi asmj index_row(1))
  next
    case False
    then show ?thesis 
      using A asmi by blast
  qed
qed

lemma tot_unimod_append_unit_vec_mat:
  fixes A :: "'a  mat"
  assumes A: "A \<in> carrier_mat nr1 n"
  assumes B: "B \<in> carrier_mat nr2 n"
  assumes "tot_unimodular A"
  assumes "\<forall> i < nr2. \<exists> j. row B i = unit_vec n j"
  shows "tot_unimodular (A @\<^sub>r B)"
  using assms(2,4)
proof(induct nr2 arbitrary: B)
  case 0
  have "A @\<^sub>r B = A" using  append_mat_empty 
    using "0"(1) assms(1) by blast
  then show ?case 
    using assms(3) by fastforce
next
  case (Suc nr2)
  have "B = (submatrix B {0..<nr2} UNIV) @\<^sub>r (mat_of_rows n [row B (nr2)])" 
    using cnoewqfqf 
    by (metis Suc(2) Suc_eq_plus1 diff_add_inverse plus_1_eq_Suc zero_less_Suc)
  have "submatrix B {0..<nr2} UNIV \<in> carrier_mat nr2 n" 
    by (metis Suc(2) diff_Suc_1 gram_schmidt_floor.pweqfh)
  have "\<forall> i < nr2. \<exists> j. row (submatrix B {0..<nr2} UNIV) i = unit_vec n j"
  proof safe
    fix i
    assume "i < nr2"
    obtain k where "row (submatrix B {0..<nr2} UNIV) i = row B k \<and> k < dim_row B" 
      by (smt (verit, best) Missing_Matrix.append_rows_nth(1) Suc(2) \<open>B = submatrix B {0..<nr2} UNIV @\<^sub>r mat_of_rows n [Matrix.row B (nr2)]\<close> \<open>i < nr2\<close> \<open>submatrix B {0..<nr2} UNIV \<in> carrier_mat nr2 n\<close> basic_trans_rules(19) carrier_matD(1) lessI mat_of_rows_carrier(1))
    then have "\<exists>j. row B k = unit_vec n j" 
      by (metis Suc(2) Suc(3) carrier_matD(1))
    
    show "\<exists>j. Matrix.row (submatrix B {0..<nr2} UNIV) i = unit_vec n j"
      using \<open>Matrix.row (submatrix B {0..<nr2} UNIV) i = Matrix.row B k \<and> k < dim_row B\<close> \<open>\<exists>j. Matrix.row B k = unit_vec n j\<close> by presburger
  qed
  have "tot_unimodular (A @\<^sub>r (submatrix B {0..<nr2} UNIV))" 
    using Suc.hyps \<open>\<forall>i<nr2. \<exists>j. Matrix.row (submatrix B {0..<nr2} UNIV) i = unit_vec n j\<close> \<open>submatrix B {0..<nr2} UNIV \<in> carrier_mat nr2 n\<close> by presburger
  have "A @\<^sub>r B = (A @\<^sub>r (submatrix B {0..<nr2} UNIV)) @\<^sub>r (mat_of_rows n [row B (nr2)])" 
    by (metis (no_types, lifting) \<open>B = submatrix B {0..<nr2} UNIV @\<^sub>r mat_of_rows n [Matrix.row B (nr2)]\<close> \<open>submatrix B {0..<nr2} UNIV \<in> carrier_mat nr2 n\<close> assms(1) mat_of_rows_carrier(1) ngwpegp)
  obtain j where "row B nr2 = unit_vec n j" 
    using Suc(3) by blast
  then have " (A @\<^sub>r (submatrix B {0..<nr2} UNIV)) @\<^sub>r (mat_of_rows n [row B (nr2)]) = 
         (A @\<^sub>r (submatrix B {0..<nr2} UNIV)) @\<^sub>r (mat_of_rows n [unit_vec n j])" 
    by presburger
  then show ?case 
    by (metis \<open>A @\<^sub>r B = (A @\<^sub>r submatrix B {0..<nr2} UNIV) @\<^sub>r mat_of_rows n [Matrix.row B nr2]\<close> \<open>submatrix B {0..<nr2} UNIV \<in> carrier_mat nr2 n\<close> \<open>tot_unimodular (A @\<^sub>r submatrix B {0..<nr2} UNIV)\<close> assms(1) carrier_append_rows gram_schmidt_floor.tot_unimod_append_unit_vec)
qed

lemma tot_unimod_append_minus_unit_vec_mat:
  fixes A :: "'a  mat"
  assumes A: "A \<in> carrier_mat nr1 n"
  assumes B: "B \<in> carrier_mat nr2 n"
  assumes "tot_unimodular A"
  assumes "\<forall> i < nr2. \<exists> j. row B i = - unit_vec n j"
  shows "tot_unimodular (A @\<^sub>r B)"
  using assms(2,4)
proof(induct nr2 arbitrary: B)
  case 0
  have "A @\<^sub>r B = A" using  append_mat_empty 
    using "0"(1) assms(1) by blast
  then show ?case 
    using assms(3) by fastforce
next
  case (Suc nr2)
  have "B = (submatrix B {0..<nr2} UNIV) @\<^sub>r (mat_of_rows n [row B (nr2)])" 
    using cnoewqfqf 
    by (metis Suc(2) Suc_eq_plus1 diff_add_inverse plus_1_eq_Suc zero_less_Suc)
  have "submatrix B {0..<nr2} UNIV \<in> carrier_mat nr2 n" 
    by (metis Suc(2) diff_Suc_1 gram_schmidt_floor.pweqfh)
  have "\<forall> i < nr2. \<exists> j. row (submatrix B {0..<nr2} UNIV) i = - unit_vec n j"
  proof safe
    fix i
    assume "i < nr2"
    obtain k where "row (submatrix B {0..<nr2} UNIV) i = row B k \<and> k < dim_row B" 
      by (smt (verit, best) Missing_Matrix.append_rows_nth(1) Suc(2) \<open>B = submatrix B {0..<nr2} UNIV @\<^sub>r mat_of_rows n [Matrix.row B (nr2)]\<close> \<open>i < nr2\<close> \<open>submatrix B {0..<nr2} UNIV \<in> carrier_mat nr2 n\<close> basic_trans_rules(19) carrier_matD(1) lessI mat_of_rows_carrier(1))
    then have "\<exists>j. row B k = - unit_vec n j" 
      by (metis Suc(2) Suc(3) carrier_matD(1))
    
    show "\<exists>j. Matrix.row (submatrix B {0..<nr2} UNIV) i = - unit_vec n j"
      using \<open>Matrix.row (submatrix B {0..<nr2} UNIV) i = Matrix.row B k \<and> k < dim_row B\<close> \<open>\<exists>j. Matrix.row B k = - unit_vec n j\<close> by presburger
  qed
  have "tot_unimodular (A @\<^sub>r (submatrix B {0..<nr2} UNIV))" 
    using Suc.hyps \<open>\<forall>i<nr2. \<exists>j. Matrix.row (submatrix B {0..<nr2} UNIV) i = - unit_vec n j\<close> \<open>submatrix B {0..<nr2} UNIV \<in> carrier_mat nr2 n\<close> by presburger
  have "A @\<^sub>r B = (A @\<^sub>r (submatrix B {0..<nr2} UNIV)) @\<^sub>r (mat_of_rows n [row B (nr2)])" 
    by (metis (no_types, lifting) \<open>B = submatrix B {0..<nr2} UNIV @\<^sub>r mat_of_rows n [Matrix.row B (nr2)]\<close> \<open>submatrix B {0..<nr2} UNIV \<in> carrier_mat nr2 n\<close> assms(1) mat_of_rows_carrier(1) ngwpegp)
  obtain j where "row B nr2 = - unit_vec n j" 
    using Suc(3) by blast
  then have " (A @\<^sub>r (submatrix B {0..<nr2} UNIV)) @\<^sub>r (mat_of_rows n [row B (nr2)]) = 
         (A @\<^sub>r (submatrix B {0..<nr2} UNIV)) @\<^sub>r (mat_of_rows n [- unit_vec n j])" 
    by presburger
  then show ?case 
    by (metis \<open>A @\<^sub>r B = (A @\<^sub>r submatrix B {0..<nr2} UNIV) @\<^sub>r mat_of_rows n [Matrix.row B nr2]\<close> \<open>submatrix B {0..<nr2} UNIV \<in> carrier_mat nr2 n\<close> \<open>tot_unimodular (A @\<^sub>r submatrix B {0..<nr2} UNIV)\<close> assms(1) carrier_append_rows gram_schmidt_floor.tot_unimod_append_minus_unit_vec)
qed

lemma tot_unimod_append_one:
fixes A :: "'a  mat"
  assumes A: "A \<in> carrier_mat nr1 n"
  assumes "tot_unimodular A"
  shows "tot_unimodular (A @\<^sub>r 1\<^sub>m n)" 
proof -
  have 1:"1\<^sub>m n \<in> carrier_mat n n" 
    by simp
  have "\<forall> i < n. row (1\<^sub>m n) i = unit_vec n i" 
    by simp
  then have 2: "\<forall> i < n. \<exists> j. row (1\<^sub>m n) i = unit_vec n j" 
    by blast
  then show ?thesis using tot_unimod_append_unit_vec_mat[OF assms(1) 1 assms(2) 2] by auto
qed

lemma tot_unimod_append_minus_one:
fixes A :: "'a  mat"
  assumes A: "A \<in> carrier_mat nr1 n" 
  assumes "tot_unimodular A"
  shows "tot_unimodular (A @\<^sub>r - 1\<^sub>m n)"
proof -
  have 1:" - 1\<^sub>m n \<in> carrier_mat n n" 
    by simp
  have "\<forall> i < n. row (- 1\<^sub>m n) i = - unit_vec n i" 
    by simp
  then have 2: "\<forall> i < n. \<exists> j. row (- 1\<^sub>m n) i = - unit_vec n j" 
    by blast
  then show ?thesis using tot_unimod_append_minus_unit_vec_mat[OF assms(1) 1 assms(2)] by auto
qed
  

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
    have 1:"?fullA \<in> carrier_mat (nr+n) n" 
      by (meson assms(1) carrier_append_rows one_carrier_mat uminus_carrier_iff_mat)
    have 2:"?fullb \<in> carrier_vec (nr+n)" 
      by (simp add: \<open>b \<in> carrier_vec nr\<close>)
    have 3:"?fullA \<in> \<int>\<^sub>m" 
      by (meson assms(1) assms(2) gram_schmidt.fegfnpp gram_schmidt.ffmoonod minus_in_Ints_mat_iff one_carrier_mat uminus_carrier_iff_mat)
    have 4:"?fullb \<in> \<int>\<^sub>v" 
      using \<open>b \<in> \<int>\<^sub>v\<close> \<open>b \<in> carrier_vec nr\<close> ffmoonffod zero_vec_is_int by blast
    have " integer_hull (polyhedron ?fullA ?fullb) = polyhedron ?fullA ?fullb"
    proof(cases "polyhedron ?fullA ?fullb = {}")
      case True
      have "integer_hull {} = {}" 
        by (simp add: integer_hull_def)
      then show ?thesis 
        using True by presburger
    next
      case False
      have 5: "\<forall>x \<in> (polyhedron ?fullA ?fullb). \<forall> i < n. x $ i \<ge>0" 
  by (smt (verit, ccfv_threshold) M.add.one_closed Matrix.less_eq_vec_def \<open>b \<in> carrier_vec nr\<close> append_rows_le assms(1) carrier_vecD dnwqofihq gram_schmidt.polyhedron_def index_mult_mat_vec index_one_mat(2) index_uminus_mat(2) index_unit_vec(3) index_zero_vec(1) mem_Collect_eq neg_le_0_iff_le one_carrier_mat one_mult_mat_vec row_one row_uminus scalar_prod_uminus_left uminus_carrier_mat)
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
        using assms(1) assms(3) tot_unimod_append_minus_one by blast
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
  oops

end