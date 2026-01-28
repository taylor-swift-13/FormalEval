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

Lemma to_binary_p_456234 : to_binary_p_rel 456234%positive "1101111011000101010".
Proof.
  replace "1101111011000101010" with ("110111101100010101" ++ "0") by reflexivity.
  apply tbp_xO.
  replace "110111101100010101" with ("11011110110001010" ++ "1") by reflexivity.
  apply tbp_xI.
  replace "11011110110001010" with ("1101111011000101" ++ "0") by reflexivity.
  apply tbp_xO.
  replace "1101111011000101" with ("110111101100010" ++ "1") by reflexivity.
  apply tbp_xI.
  replace "110111101100010" with ("11011110110001" ++ "0") by reflexivity.
  apply tbp_xO.
  replace "11011110110001" with ("1101111011000" ++ "1") by reflexivity.
  apply tbp_xI.
  replace "1101111011000" with ("110111101100" ++ "0") by reflexivity.
  apply tbp_xO.
  replace "110111101100" with ("11011110110" ++ "0") by reflexivity.
  apply tbp_xO.
  replace "11011110110" with ("1101111011" ++ "0") by reflexivity.
  apply tbp_xO.
  replace "1101111011" with ("110111101" ++ "1") by reflexivity.
  apply tbp_xI.
  replace "110111101" with ("11011110" ++ "1") by reflexivity.
  apply tbp_xI.
  replace "11011110" with ("1101111" ++ "0") by reflexivity.
  apply tbp_xO.
  replace "1101111" with ("110111" ++ "1") by reflexivity.
  apply tbp_xI.
  replace "110111" with ("11011" ++ "1") by reflexivity.
  apply tbp_xI.
  replace "11011" with ("1101" ++ "1") by reflexivity.
  apply tbp_xI.
  replace "1101" with ("110" ++ "1") by reflexivity.
  apply tbp_xI.
  replace "110" with ("11" ++ "0") by reflexivity.
  apply tbp_xO.
  replace "11" with ("1" ++ "1") by reflexivity.
  apply tbp_xI.
  apply tbp_xH.
Qed.

Example test_problem_103 : problem_103_spec 123456 789012 (Binary "0b1101111011000101010").
Proof.
  unfold problem_103_spec.
  right.
  exists 912468%Z, 2%Z, 456234%Z, "0b1101111011000101010".
  split.
  - lia.
  - split.
    + reflexivity.
    + split.
      * replace "0b1101111011000101010" with ("0b" ++ "1101111011000101010") by reflexivity.
        apply tbr_pos.
        apply to_binary_p_456234.
      * reflexivity.
Qed.