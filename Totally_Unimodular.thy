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

lemma fcdnwe:
   fixes A :: "'a  mat"
   assumes A: "A \<in> carrier_mat nr1 n" 
   assumes B: "B \<in> carrier_mat nr2 n"
   shows "submatrix (A @\<^sub>r B) I J =
          submatrix A I J @\<^sub>r submatrix B ((\<lambda> i. i - nr1) ` (I - {0..<nr1})) J"
  sorry

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
  sorry

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

    have "B = submatrix A I J @\<^sub>r submatrix (mat_of_rows n [unit_vec n i]) (?f ` (I - {0..<nr})) J"
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
      have "det B = (\<Sum>j<dim_row B. B $$ (dim_row B - 1,j) * cofactor B (dim_row B - 1) j)"
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
     
    

      then show ?thesis sorry
    next
      case False
      then show ?thesis sorry
    qed
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