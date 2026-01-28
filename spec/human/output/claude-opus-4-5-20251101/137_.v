Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Reals.Reals.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.
Open Scope R_scope.

(* ==================== 输入类型 ==================== *)

(* 三种输入类型：整数、浮点数、字符串 *)
Inductive val :=
| VInt : Z -> val
| VFloat : R -> val
| VStr : string -> val.

(* ==================== 字符判断谓词 ==================== *)

(* 判断是否是十进制数字字符 '0'-'9' *)
Definition is_digit (c : ascii) : bool :=
  let n := nat_of_ascii c in
  andb (48 <=? n)%nat (n <=? 57)%nat.

(* 将数字字符转换为其数值 0..9 *)
Definition digit_val (c : ascii) : nat :=
  Nat.sub (nat_of_ascii c) 48.

(* 判断是否为小数点分隔符 '.' (ASCII 46) 或 ',' (ASCII 44) *)
Definition is_sep (c : ascii) : bool :=
  let n := nat_of_ascii c in
  orb (Nat.eqb n 46) (Nat.eqb n 44).

(* 判断是否为负号 '-' (ASCII 45) *)
Definition is_minus (c : ascii) : bool :=
  Nat.eqb (nat_of_ascii c) 45.

(* 判断是否为正号 '+' (ASCII 43) *)
Definition is_plus (c : ascii) : bool :=
  Nat.eqb (nat_of_ascii c) 43.

(* ==================== 数字解析关系 ==================== *)

Inductive digits_to_nat : list ascii -> nat -> nat -> Prop :=
| dtn_nil : forall acc,
    digits_to_nat [] acc acc
| dtn_cons : forall c tl acc result,
    is_digit c = true ->
    digits_to_nat tl (acc * 10 + digit_val c) result ->
    digits_to_nat (c :: tl) acc result.

(* ==================== 字符串分割关系 ==================== *)

Inductive split_on_sep : list ascii -> list ascii -> list ascii -> Prop :=
| sos_nil :
    split_on_sep [] [] []
| sos_sep : forall c tl,
    is_sep c = true ->
    split_on_sep (c :: tl) [] tl
| sos_cons : forall c tl int_part frac_part,
    is_sep c = false ->
    split_on_sep tl int_part frac_part ->
    split_on_sep (c :: tl) (c :: int_part) frac_part.

(* ==================== 10 的幂次关系 ==================== *)

Inductive pow10 : nat -> R -> Prop :=
| pow10_O :
    pow10 0%nat 1%R
| pow10_S : forall n p,
    pow10 n p ->
    pow10 (S n) (10 * p)%R.

(* ==================== 字符串解析关系 ==================== *)

Inductive parse_string : string -> bool -> nat -> nat -> nat -> Prop :=
| ps_neg_with_frac : forall s c rest int_chars frac_chars int_v frac_v,
    list_ascii_of_string s = c :: rest ->
    is_minus c = true ->
    split_on_sep rest int_chars frac_chars ->
    int_chars <> [] ->
    frac_chars <> [] ->
    digits_to_nat int_chars 0 int_v ->
    digits_to_nat frac_chars 0 frac_v ->
    parse_string s true int_v frac_v (length frac_chars)
| ps_neg_no_frac : forall s c rest int_chars int_v,
    list_ascii_of_string s = c :: rest ->
    is_minus c = true ->
    split_on_sep rest int_chars [] ->
    int_chars <> [] ->
    digits_to_nat int_chars 0 int_v ->
    parse_string s true int_v 0 0
| ps_pos_with_frac : forall s c rest int_chars frac_chars int_v frac_v,
    list_ascii_of_string s = c :: rest ->
    is_plus c = true ->
    split_on_sep rest int_chars frac_chars ->
    int_chars <> [] ->
    frac_chars <> [] ->
    digits_to_nat int_chars 0 int_v ->
    digits_to_nat frac_chars 0 frac_v ->
    parse_string s false int_v frac_v (length frac_chars)
| ps_pos_no_frac : forall s c rest int_chars int_v,
    list_ascii_of_string s = c :: rest ->
    is_plus c = true ->
    split_on_sep rest int_chars [] ->
    int_chars <> [] ->
    digits_to_nat int_chars 0 int_v ->
    parse_string s false int_v 0 0
| ps_no_sign_with_frac : forall s chars int_chars frac_chars int_v frac_v c rest,
    list_ascii_of_string s = chars ->
    chars = c :: rest ->
    is_minus c = false ->
    is_plus c = false ->
    split_on_sep chars int_chars frac_chars ->
    int_chars <> [] ->
    frac_chars <> [] ->
    digits_to_nat int_chars 0 int_v ->
    digits_to_nat frac_chars 0 frac_v ->
    parse_string s false int_v frac_v (length frac_chars)
| ps_no_sign_no_frac : forall s chars int_chars int_v c rest,
    list_ascii_of_string s = chars ->
    chars = c :: rest ->
    is_minus c = false ->
    is_plus c = false ->
    split_on_sep chars int_chars [] ->
    int_chars <> [] ->
    digits_to_nat int_chars 0 int_v ->
    parse_string s false int_v 0 0.

(* ==================== 字符串表示实数关系 ==================== *)

Inductive str_represents : string -> R -> Prop :=
| sr_positive : forall s int_v frac_v frac_len p,
    parse_string s false int_v frac_v frac_len ->
    pow10 frac_len p ->
    str_represents s (INR int_v + (if (frac_len =? 0)%nat then 0 else INR frac_v / p))%R
| sr_negative : forall s int_v frac_v frac_len p,
    parse_string s true int_v frac_v frac_len ->
    pow10 frac_len p ->
    str_represents s (- (INR int_v + (if (frac_len =? 0)%nat then 0 else INR frac_v / p)))%R.

(* ==================== 值转换关系 ==================== *)

Inductive value_of : val -> R -> Prop :=
| vo_int : forall z,
    value_of (VInt z) (IZR z)
| vo_float : forall r,
    value_of (VFloat r) r
| vo_str : forall s r,
    str_represents s r ->
    value_of (VStr s) r.

(* ==================== 实数比较关系 ==================== *)

Inductive Rcompare : R -> R -> comparison -> Prop :=
| Rcmp_lt : forall x y,
    (x < y)%R ->
    Rcompare x y Lt
| Rcmp_eq : forall x y,
    (x = y)%R ->
    Rcompare x y Eq
| Rcmp_gt : forall x y,
    (x > y)%R ->
    Rcompare x y Gt.

(* ==================== 主规范 ==================== *)

Definition problem_137_pre (a b : val) : Prop := True.

Inductive problem_137_spec : val -> val -> option val -> Prop :=
| spec_a_lt_b : forall a b ra rb,
    value_of a ra ->
    value_of b rb ->
    Rcompare ra rb Lt ->
    problem_137_spec a b (Some b)
| spec_a_gt_b : forall a b ra rb,
    value_of a ra ->
    value_of b rb ->
    Rcompare ra rb Gt ->
    problem_137_spec a b (Some a)
| spec_a_eq_b : forall a b ra rb,
    value_of a ra ->
    value_of b rb ->
    Rcompare ra rb Eq ->
    problem_137_spec a b None.

(* Test case: compare_one(1, 2) returns 2 (the larger value) *)
Example test_compare_one_1_2 :
  problem_137_spec (VInt 1%Z) (VInt 2%Z) (Some (VInt 2%Z)).
Proof.
  apply spec_a_lt_b with (ra := IZR 1%Z) (rb := IZR 2%Z).
  - apply vo_int.
  - apply vo_int.
  - apply Rcmp_lt.
    apply IZR_lt.
    lia.
Qed.