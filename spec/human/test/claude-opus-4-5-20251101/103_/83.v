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

Lemma to_binary_p_11000 : to_binary_p_rel 11000%positive "10101011111000".
Proof.
  unfold Pos.of_nat.
  replace "10101011111000" with ("1010101111100" ++ "0") by reflexivity.
  apply tbp_xO.
  replace "1010101111100" with ("101010111110" ++ "0") by reflexivity.
  apply tbp_xO.
  replace "101010111110" with ("10101011111" ++ "0") by reflexivity.
  apply tbp_xO.
  replace "10101011111" with ("1010101111" ++ "1") by reflexivity.
  apply tbp_xI.
  replace "1010101111" with ("101010111" ++ "1") by reflexivity.
  apply tbp_xI.
  replace "101010111" with ("10101011" ++ "1") by reflexivity.
  apply tbp_xI.
  replace "10101011" with ("1010101" ++ "1") by reflexivity.
  apply tbp_xI.
  replace "1010101" with ("101010" ++ "1") by reflexivity.
  apply tbp_xI.
  replace "101010" with ("10101" ++ "0") by reflexivity.
  apply tbp_xO.
  replace "10101" with ("1010" ++ "1") by reflexivity.
  apply tbp_xI.
  replace "1010" with ("101" ++ "0") by reflexivity.
  apply tbp_xO.
  replace "101" with ("10" ++ "1") by reflexivity.
  apply tbp_xI.
  replace "10" with ("1" ++ "0") by reflexivity.
  apply tbp_xO.
  apply tbp_xH.
Qed.

Example test_problem_103 : problem_103_spec 10000 12000 (Binary "0b10101011111000").
Proof.
  unfold problem_103_spec.
  right.
  exists 22000%Z, 2001%Z, 11000%Z, "0b10101011111000".
  split.
  - lia.
  - split.
    + reflexivity.
    + split.
      * replace "0b10101011111000" with ("0b" ++ "10101011111000") by reflexivity.
        apply tbr_pos.
        apply to_binary_p_11000.
      * reflexivity.
Qed.