theory Missing_Matrix
  imports
          Subsystems
begin

lemma rows_append_append_lists:
  assumes A: "A \<in> carrier_mat nr1 n" 
  assumes B: "B \<in> carrier_mat nr2 n" 
  shows "rows (A @\<^sub>r B) = (rows A) @ (rows B)"
proof -
  have 0:"length (rows (A @\<^sub>r B)) = length (rows A) + length (rows B)"
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
        by (metis A 0 
            add_diff_inverse_nat assms(2) carrier_matD(1) le_add1 length_rows nth_rows)
      moreover have "((rows A) @ (rows B)) ! i = (rows B) ! (i-nr1)"
        by (metis False assms(1) carrier_matD(1) length_rows nth_append)
      then show ?thesis
        by (metis False 0 add_diff_cancel_left' asmi assms(1) calculation carrier_matD(1) 
            le_add_diff_inverse2 length_rows less_diff_conv not_le nth_rows)
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

lemma last_row_submatrix:
  assumes A: "A \<in> carrier_mat nr n" 
  assumes "nr - 1 \<in> I"
  shows "row (submatrix A I UNIV) (dim_row (submatrix A I UNIV) - 1) = row A (nr-1)"
proof(cases "nr = 0")
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
  have 2:"row (submatrix A I UNIV) ?i = row A (pick I ?i)"
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
    using 2 by presburger
qed
end