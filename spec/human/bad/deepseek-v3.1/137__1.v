(* ==================== 字符串转换函数 ==================== *)

Definition list_ascii_of_string (s : string) : list ascii :=
  let fix aux s :=
    match s with
    | EmptyString => []
    | String c s' => c :: aux s'
    end in
  aux s.

(* ==================== 辅助引理 ==================== *)

Lemma digits_to_nat_sound : forall chars acc result,
  digits_to_nat chars acc result ->
  result = fold_left (fun a c => 10 * a + digit_val c) chars acc.
Proof.
  intros chars acc result H.
  induction H.
  - reflexivity.
  - simpl. rewrite IHdigits_to_nat. reflexivity.
Qed.

Lemma pow10_sound : forall n p,
  pow10 n p -> p = (10 ^ n)%R.
Proof.
  intros n p H.
  induction H.
  - simpl. lra.
  - rewrite IHpow10. simpl. lra.
Qed.

Lemma Rcompare_sound : forall x y cmp,
  Rcompare x y cmp ->
  match cmp with
  | Lt => (x < y)%R
  | Eq => (x = y)%R
  | Gt => (x > y)%R
  end.
Proof.
  intros x y cmp H.
  inversion H; subst.
  - lra.
  - lra.
  - lra.
Qed.

(* ==================== 测试用例证明 ==================== *)

Example test_case_1_2 : problem_137_spec (VInt 1) (VInt 2) (Some (VInt 2)).
Proof.
  (* 应用 a < b 的规范 *)
  apply spec_a_lt_b with (ra := 1%R) (rb := 2%R).
  - (* 证明 value_of (VInt 1) 1 *)
    apply vo_int.
  - (* 证明 value_of (VInt 2) 2 *)
    apply vo_int.
  - (* 证明 Rcompare 1 2 Lt *)
    apply Rcmp_lt.
    lra.
Qed.

(* ==================== 其他测试用例 ==================== *)

(* 测试用例: compare_one(1, 2.5) ➞ 2.5 *)
Example test_case_1_2p5 : problem_137_spec (VInt 1) (VFloat 2.5) (Some (VFloat 2.5)).
Proof.
  apply spec_a_lt_b with (ra := 1%R) (rb := 2.5%R).
  - apply vo_int.
  - apply vo_float.
  - apply Rcmp_lt. lra.
Qed.

(* 测试用例: compare_one("1", 1) ➞ None *)
Example test_case_str1_int1 : problem_137_spec (VStr "1") (VInt 1) None.
Proof.
  (* 首先需要证明 "1" 表示实数 1 *)
  assert (str_represents "1" 1%R).
  {
    apply sr_positive with (int_v := 1) (frac_v := 0) (frac_len := 0) (p := 1%R).
    - apply ps_no_sign_no_frac with (chars := [ "1"%char ]) (int_chars := [ "1"%char ]) (c := "1"%char).
      + reflexivity.
      + reflexivity.
      + compute; auto.
      + compute; auto.
      + apply sos_cons with (c := "1"%char) (tl := []).
        * compute; auto.
        * apply sos_nil.
      + compute; auto.
      + apply dtn_cons with (c := "1"%char) (tl := []) (acc := 0) (result := 1).
        * compute; auto.
        * apply dtn_nil.
    - apply pow10_O.
  }
  
  apply spec_a_eq_b with (ra := 1%R) (rb := 1%R).
  - apply vo_str. apply H.
  - apply vo_int.
  - apply Rcmp_eq. lra.
Qed.

(* ==================== 字符串解析示例 ==================== *)

(* 证明 "2,3" 表示 2.3 *)
Example str_2comma3_represents_2p3 : str_represents "2,3" 2.3%R.
Proof.
  apply sr_positive with (int_v := 2) (frac_v := 3) (frac_len := 1) (p := 10%R).
  - apply ps_no_sign_with_frac with (chars := ["2"; ","; "3"]) (int_chars := ["2"]) (frac_chars := ["3"]) (c := "2"%char).
    + reflexivity.
    + reflexivity.
    + compute; auto.
    + compute; auto.
    + apply sos_cons with (c := "2"%char) (tl := [","; "3"]).
      * compute; auto.
      * apply sos_sep with (c := ","%char) (tl := ["3"]).
        compute; auto.
    + compute; auto.
    + compute; auto.
    + apply dtn_cons with (c := "2"%char) (tl := []) (acc := 0) (result := 2).
      * compute; auto.
      * apply dtn_nil.
    + apply dtn_cons with (c := "3"%char) (tl := []) (acc := 0) (result := 3).
      * compute; auto.
      * apply dtn_nil.
  - apply pow10_S with (n := 0%nat) (p := 1%R).
    apply pow10_O.
Qed.

(* 测试用例: compare_one(1, "2,3") ➞ "2,3" *)
Example test_case_1_str23 : problem_137_spec (VInt 1) (VStr "2,3") (Some (VStr "2,3")).
Proof.
  apply spec_a_lt_b with (ra := 1%R) (rb := 2.3%R).
  - apply vo_int.
  - apply vo_str. apply str_2comma3_represents_2p3.
  - apply Rcmp_lt. lra.
Qed.

(* ==================== 负数字符串示例 ==================== *)

(* 证明 "-1.5" 表示 -1.5 *)
Example str_neg1p5_represents_neg1p5 : str_represents "-1.5" (-1.5)%R.
Proof.
  apply sr_negative with (int_v := 1) (frac_v := 5) (frac_len := 1) (p := 10%R).
  - apply ps_neg_with_frac with (s := "-1.5") (c := "-"%char) (rest := ["1"; "."; "5"]) 
                                (int_chars := ["1"]) (frac_chars := ["5"]).
    + reflexivity.
    + compute; auto.
    + apply sos_cons with (c := "1"%char) (tl := ["."; "5"]).
      * compute; auto.
      * apply sos_sep with (c := "."%char) (tl := ["5"]).
        compute; auto.
    + compute; auto.
    + compute; auto.
    + apply dtn_cons with (c := "1"%char) (tl := []) (acc := 0) (result := 1).
      * compute; auto.
      * apply dtn_nil.
    + apply dtn_cons with (c := "5"%char) (tl := []) (acc := 0) (result := 5).
      * compute; auto.
      * apply dtn_nil.
  - apply pow10_S with (n := 0%nat) (p := 1%R).
    apply pow10_O.
Qed.

(* ==================== 补充测试用例 ==================== *)

(* 测试用例: compare_one("5,1", "6") ➞ "6" *)
Example test_case_str51_str6 : problem_137_spec (VStr "5,1") (VStr "6") (Some (VStr "6")).
Proof.
  (* 首先证明 "5,1" 表示 5.1 *)
  assert (H1: str_represents "5,1" 5.1%R).
  {
    apply sr_positive with (int_v := 5) (frac_v := 1) (frac_len := 1) (p := 10%R).
    - apply ps_no_sign_with_frac with (chars := ["5"; ","; "1"]) (int_chars := ["5"]) (frac_chars := ["1"]) (c := "5"%char).
      + reflexivity.
      + reflexivity.
      + compute; auto.
      + compute; auto.
      + apply sos_cons with (c := "5"%char) (tl := [","; "1"]).
        * compute; auto.
        * apply sos_sep with (c := ","%char) (tl := ["1"]).
          compute; auto.
      + compute; auto.
      + compute; auto.
      + apply dtn_cons with (c := "5"%char) (tl := []) (acc := 0) (result := 5).
        * compute; auto.
        * apply dtn_nil.
      + apply dtn_cons with (c := "1"%char) (tl := []) (acc := 0) (result := 1).
        * compute; auto.
        * apply dtn_nil.
    - apply pow10_S with (n := 0%nat) (p := 1%R).
      apply pow10_O.
  }
  
  (* 然后证明 "6" 表示 6 *)
  assert (H2: str_represents "6" 6%R).
  {
    apply sr_positive with (int_v := 6) (frac_v := 0) (frac_len := 0) (p := 1%R).
    - apply ps_no_sign_no_frac with (chars := ["6"]) (int_chars := ["6"]) (c := "6"%char).
      + reflexivity.
      + reflexivity.
      + compute; auto.
      + compute; auto.
      + apply sos_cons with (c := "6"%char) (tl := []).
        * compute; auto.
        * apply sos_nil.
      + compute; auto.
      + apply dtn_cons with (c := "6"%char) (tl := []) (acc := 0) (result := 6).
        * compute; auto.
        * apply dtn_nil.
    - apply pow10_O.
  }
  
  apply spec_a_lt_b with (ra := 5.1%R) (rb := 6%R).
  - apply vo_str. apply H1.
  - apply vo_str. apply H2.
  - apply Rcmp_lt. lra.
Qed.

(* ==================== 相等情况测试 ==================== *)

(* 测试用例: 两个相同的整数 *)
Example test_case_equal_ints : problem_137_spec (VInt 5) (VInt 5) None.
Proof.
  apply spec_a_eq_b with (ra := 5%R) (rb := 5%R).
  - apply vo_int.
  - apply vo_int.
  - apply Rcmp_eq. lra.
Qed.

(* ==================== 主要测试用例证明结束 ==================== *)