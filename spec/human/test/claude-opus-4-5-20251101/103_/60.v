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

Lemma to_binary_p_150 : to_binary_p_rel 150%positive "10010110".
Proof.
  replace "10010110" with ("1001011" ++ "0") by reflexivity.
  apply tbp_xO.
  replace "1001011" with ("100101" ++ "1") by reflexivity.
  apply tbp_xI.
  replace "100101" with ("10010" ++ "1") by reflexivity.
  apply tbp_xI.
  replace "10010" with ("1001" ++ "0") by reflexivity.
  apply tbp_xO.
  replace "1001" with ("100" ++ "1") by reflexivity.
  apply tbp_xI.
  replace "100" with ("10" ++ "0") by reflexivity.
  apply tbp_xO.
  replace "10" with ("1" ++ "0") by reflexivity.
  apply tbp_xO.
  apply tbp_xH.
Qed.

Example test_problem_103 : problem_103_spec 101 200 (Binary "0b10010110").
Proof.
  unfold problem_103_spec.
  right.
  exists 301%Z, 100%Z, 150%Z, "0b10010110".
  split.
  - lia.
  - split.
    + reflexivity.
    + split.
      * replace "0b10010110" with ("0b" ++ "10010110") by reflexivity.
        apply tbr_pos.
        apply to_binary_p_150.
      * reflexivity.
Qed.