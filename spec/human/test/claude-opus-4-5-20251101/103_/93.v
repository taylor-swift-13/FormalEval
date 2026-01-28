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

Lemma to_binary_p_501500 : to_binary_p_rel 501500%positive "1111010011011111100".
Proof.
  unfold Pos.of_nat.
  replace "1111010011011111100" with ("111101001101111110" ++ "0") by reflexivity.
  apply tbp_xO.
  replace "111101001101111110" with ("11110100110111111" ++ "0") by reflexivity.
  apply tbp_xO.
  replace "11110100110111111" with ("1111010011011111" ++ "1") by reflexivity.
  apply tbp_xI.
  replace "1111010011011111" with ("111101001101111" ++ "1") by reflexivity.
  apply tbp_xI.
  replace "111101001101111" with ("11110100110111" ++ "1") by reflexivity.
  apply tbp_xI.
  replace "11110100110111" with ("1111010011011" ++ "1") by reflexivity.
  apply tbp_xI.
  replace "1111010011011" with ("111101001101" ++ "1") by reflexivity.
  apply tbp_xI.
  replace "111101001101" with ("11110100110" ++ "1") by reflexivity.
  apply tbp_xI.
  replace "11110100110" with ("1111010011" ++ "0") by reflexivity.
  apply tbp_xO.
  replace "1111010011" with ("111101001" ++ "1") by reflexivity.
  apply tbp_xI.
  replace "111101001" with ("11110100" ++ "1") by reflexivity.
  apply tbp_xI.
  replace "11110100" with ("1111010" ++ "0") by reflexivity.
  apply tbp_xO.
  replace "1111010" with ("111101" ++ "0") by reflexivity.
  apply tbp_xO.
  replace "111101" with ("11110" ++ "1") by reflexivity.
  apply tbp_xI.
  replace "11110" with ("1111" ++ "0") by reflexivity.
  apply tbp_xO.
  replace "1111" with ("111" ++ "1") by reflexivity.
  apply tbp_xI.
  replace "111" with ("11" ++ "1") by reflexivity.
  apply tbp_xI.
  replace "11" with ("1" ++ "1") by reflexivity.
  apply tbp_xI.
  apply tbp_xH.
Qed.

Example test_problem_103 : problem_103_spec 3000 1000000 (Binary "0b1111010011011111100").
Proof.
  unfold problem_103_spec.
  right.
  exists 1003000%Z, 997001%Z, 501500%Z, "0b1111010011011111100".
  split.
  - lia.
  - split.
    + reflexivity.
    + split.
      * replace "0b1111010011011111100" with ("0b" ++ "1111010011011111100") by reflexivity.
        apply tbr_pos.
        apply to_binary_p_501500.
      * reflexivity.
Qed.