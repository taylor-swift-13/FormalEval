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

Lemma to_binary_p_4000 : to_binary_p_rel 4000%positive "111110100000".
Proof.
  replace "111110100000" with ("11111010000" ++ "0") by reflexivity.
  apply tbp_xO.
  replace "11111010000" with ("1111101000" ++ "0") by reflexivity.
  apply tbp_xO.
  replace "1111101000" with ("111110100" ++ "0") by reflexivity.
  apply tbp_xO.
  replace "111110100" with ("11111010" ++ "0") by reflexivity.
  apply tbp_xO.
  replace "11111010" with ("1111101" ++ "0") by reflexivity.
  apply tbp_xO.
  replace "1111101" with ("111110" ++ "1") by reflexivity.
  apply tbp_xI.
  replace "111110" with ("11111" ++ "0") by reflexivity.
  apply tbp_xO.
  replace "11111" with ("1111" ++ "1") by reflexivity.
  apply tbp_xI.
  replace "1111" with ("111" ++ "1") by reflexivity.
  apply tbp_xI.
  replace "111" with ("11" ++ "1") by reflexivity.
  apply tbp_xI.
  replace "11" with ("1" ++ "1") by reflexivity.
  apply tbp_xI.
  apply tbp_xH.
Qed.

Example test_problem_103 : problem_103_spec 3000 5000 (Binary "0b111110100000").
Proof.
  unfold problem_103_spec.
  right.
  exists 8000%Z, 2001%Z, 4000%Z, "0b111110100000".
  split.
  - lia.
  - split.
    + reflexivity.
    + split.
      * replace "0b111110100000" with ("0b" ++ "111110100000") by reflexivity.
        apply tbr_pos.
        apply to_binary_p_4000.
      * reflexivity.
Qed.