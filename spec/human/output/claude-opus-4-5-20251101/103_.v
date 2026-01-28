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

(* Helper lemma to show to_binary_p_rel for 3 = xI xH *)
Lemma to_binary_p_3 : to_binary_p_rel 3%positive "11".
Proof.
  (* 3 = xI xH, so we need to show to_binary_p_rel (xI xH) "11" *)
  (* Using tbp_xI with p' = xH and s' = "1" *)
  replace "11" with ("1" ++ "1") by reflexivity.
  apply tbp_xI.
  apply tbp_xH.
Qed.

(* Main example proof *)
Example test_problem_103 : problem_103_spec 1 5 (Binary "0b11").
Proof.
  unfold problem_103_spec.
  right.
  exists 15%Z, 5%Z, 3%Z, "0b11".
  split.
  - lia.
  - split.
    + reflexivity.
    + split.
      * (* to_binary_rel 3 "0b11" *)
        replace "0b11" with ("0b" ++ "11") by reflexivity.
        apply tbr_pos.
        apply to_binary_p_3.
      * reflexivity.
Qed.