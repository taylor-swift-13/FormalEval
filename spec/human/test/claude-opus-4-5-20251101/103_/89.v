(* 引入所需的库 *)
Require Import ZArith.
Require Import String.
Require Import PArith.
Require Import Lia.
Open Scope Z_scope.
Open Scope string_scope.

(* 定义一个表示输出的类型：可以是二进制字符串或-1 *)
Inductive result : Type :=
  | Binary : string -> result
  | NegativeOne : result.

Inductive to_binary_p_rel : positive -> string -> Prop :=
  | tbp_xH : to_binary_p_rel xH "1"
  | tbp_xO : forall p' s', to_binary_p_rel p' s' -> to_binary_p_rel (xO p') (s' ++ "0")
  | tbp_xI : forall p' s', to_binary_p_rel p' s' -> to_binary_p_rel (xI p') (s' ++ "1").

Inductive to_binary_rel : Z -> string -> Prop :=
  | tbr_zero : to_binary_rel Z0 "0b0"
  | tbr_pos : forall p s, to_binary_p_rel p s -> to_binary_rel (Zpos p) ("0b" ++ s)
  | tbr_neg : forall p, to_binary_rel (Zneg p) "Error: Negative numbers not supported".


(* n 与 m 为正整数 *)
Definition problem_103_pre (n m : Z) : Prop := n > 0 /\ m > 0.

Definition problem_103_spec (n m : Z) (output : result) : Prop :=
  (n > m /\ output = NegativeOne) \/
  (exists (sum : Z) (count : Z) (rounded_avg : Z) (bin_str : string),
     n <= m /\
     rounded_avg = (n + m) / 2 /\
     to_binary_rel rounded_avg bin_str /\
     output = Binary bin_str).

Lemma to_binary_p_100000 : to_binary_p_rel 100000%positive "11000011010100000".
Proof.
  unfold Pos.of_nat.
  replace "11000011010100000" with ("1100001101010000" ++ "0") by reflexivity.
  apply tbp_xO.
  replace "1100001101010000" with ("110000110101000" ++ "0") by reflexivity.
  apply tbp_xO.
  replace "110000110101000" with ("11000011010100" ++ "0") by reflexivity.
  apply tbp_xO.
  replace "11000011010100" with ("1100001101010" ++ "0") by reflexivity.
  apply tbp_xO.
  replace "1100001101010" with ("110000110101" ++ "0") by reflexivity.
  apply tbp_xO.
  replace "110000110101" with ("11000011010" ++ "1") by reflexivity.
  apply tbp_xI.
  replace "11000011010" with ("1100001101" ++ "0") by reflexivity.
  apply tbp_xO.
  replace "1100001101" with ("110000110" ++ "1") by reflexivity.
  apply tbp_xI.
  replace "110000110" with ("11000011" ++ "0") by reflexivity.
  apply tbp_xO.
  replace "11000011" with ("1100001" ++ "1") by reflexivity.
  apply tbp_xI.
  replace "1100001" with ("110000" ++ "1") by reflexivity.
  apply tbp_xI.
  replace "110000" with ("11000" ++ "0") by reflexivity.
  apply tbp_xO.
  replace "11000" with ("1100" ++ "0") by reflexivity.
  apply tbp_xO.
  replace "1100" with ("110" ++ "0") by reflexivity.
  apply tbp_xO.
  replace "110" with ("11" ++ "0") by reflexivity.
  apply tbp_xO.
  replace "11" with ("1" ++ "1") by reflexivity.
  apply tbp_xI.
  apply tbp_xH.
Qed.

Example test_problem_103 : problem_103_spec 99998 100003 (Binary "0b11000011010100000").
Proof.
  unfold problem_103_spec.
  right.
  exists 200001%Z, 6%Z, 100000%Z, "0b11000011010100000".
  split.
  - lia.
  - split.
    + reflexivity.
    + split.
      * replace "0b11000011010100000" with ("0b" ++ "11000011010100000") by reflexivity.
        apply tbr_pos.
        apply to_binary_p_100000.
      * reflexivity.
Qed.