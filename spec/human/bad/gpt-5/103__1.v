(* You are given two positive integers n and m, and your task is to compute the
average of the integers from n through m (including n and m).
Round the answer to the nearest integer and convert that to binary.
If n is greater than m, return -1.
Example:
rounded_avg(1, 5) => "0b11"
rounded_avg(7, 5) => -1
rounded_avg(10, 20) => "0b1111"
rounded_avg(20, 33) => "0b11010" *)

Require Import ZArith.
Require Import String.
Require Import PArith.
Require Import Lia.
Open Scope Z_scope.
Open Scope string_scope.

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

Definition problem_103_pre (n m : Z) : Prop := n > 0 /\ m > 0.

Definition problem_103_spec (n m : Z) (output : result) : Prop :=
  (n > m /\ output = NegativeOne) \/
  (exists (sum : Z) (count : Z) (rounded_avg : Z) (bin_str : string),
     n <= m /\
     rounded_avg = (n + m) / 2 /\
     to_binary_rel rounded_avg bin_str /\
     output = Binary bin_str).

Example problem_103_test_case_1_pre : problem_103_pre 1%Z 5%Z.
Proof.
  unfold problem_103_pre.
  split; lia.
Qed.

Example problem_103_test_case_1_spec : problem_103_spec 1%Z 5%Z (Binary "0b11").
Proof.
  unfold problem_103_spec.
  right.
  exists 0%Z.
  exists 0%Z.
  exists 3%Z.
  exists "0b11".
  split.
  - lia.
  split.
  - vm_compute; reflexivity.
  split.
  - (* to_binary_rel 3 "0b11" *)
    apply (tbr_pos (xI xH) "11").
    change "11" with ("1" ++ "1").
    apply tbp_xI.
    apply tbp_xH.
  - reflexivity.
Qed.