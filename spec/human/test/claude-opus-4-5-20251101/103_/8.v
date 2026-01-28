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

Lemma to_binary_p_626 : to_binary_p_rel 626%positive "1001110010".
Proof.
  replace "1001110010" with ("100111001" ++ "0") by reflexivity.
  apply tbp_xO.
  replace "100111001" with ("10011100" ++ "1") by reflexivity.
  apply tbp_xI.
  replace "10011100" with ("1001110" ++ "0") by reflexivity.
  apply tbp_xO.
  replace "1001110" with ("100111" ++ "0") by reflexivity.
  apply tbp_xO.
  replace "100111" with ("10011" ++ "1") by reflexivity.
  apply tbp_xI.
  replace "10011" with ("1001" ++ "1") by reflexivity.
  apply tbp_xI.
  replace "1001" with ("100" ++ "1") by reflexivity.
  apply tbp_xI.
  replace "100" with ("10" ++ "0") by reflexivity.
  apply tbp_xO.
  replace "10" with ("1" ++ "0") by reflexivity.
  apply tbp_xO.
  apply tbp_xH.
Qed.

Example test_problem_103 : problem_103_spec 350 902 (Binary "0b1001110010").
Proof.
  unfold problem_103_spec.
  right.
  exists 1252%Z, 553%Z, 626%Z, "0b1001110010".
  split.
  - lia.
  - split.
    + reflexivity.
    + split.
      * replace "0b1001110010" with ("0b" ++ "1001110010") by reflexivity.
        apply tbr_pos.
        apply to_binary_p_626.
      * reflexivity.
Qed.