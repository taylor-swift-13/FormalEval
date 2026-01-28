(* Import necessary libraries *)
Require Import ZArith.
Require Import String.
Require Import PArith.
Require Import Psatz.

Open Scope Z_scope.
Open Scope string_scope.

(* Define the result type *)
Inductive result : Type :=
  | Binary : string -> result
  | NegativeOne : result.

(* Define the binary conversion relation for positive numbers *)
Inductive to_binary_p_rel : positive -> string -> Prop :=
  | tbp_xH : to_binary_p_rel xH "1"
  | tbp_xO : forall p' s', to_binary_p_rel p' s' -> to_binary_p_rel (xO p') (s' ++ "0")
  | tbp_xI : forall p' s', to_binary_p_rel p' s' -> to_binary_p_rel (xI p') (s' ++ "1").

(* Define the binary conversion relation for integers *)
Inductive to_binary_rel : Z -> string -> Prop :=
  | tbr_zero : to_binary_rel Z0 "0b0"
  | tbr_pos : forall p s, to_binary_p_rel p s -> to_binary_rel (Zpos p) ("0b" ++ s)
  | tbr_neg : forall p, to_binary_rel (Zneg p) "Error: Negative numbers not supported".

(* Precondition for the problem: n and m are positive integers *)
Definition problem_103_pre (n m : Z) : Prop := n > 0 /\ m > 0.

(* Specification for the problem *)
Definition problem_103_spec (n m : Z) (output : result) : Prop :=
  (n > m /\ output = NegativeOne) \/
  (exists rounded_avg bin_str,
     n <= m /\
     rounded_avg = (n + m) / 2 /\
     to_binary_rel rounded_avg bin_str /\
     output = Binary bin_str).

(* Example proof for the test case: input = [1%Z; 5%Z], output = "0b11" *)
Example rounded_avg_example : problem_103_spec 1 5 (Binary "0b11").
Proof.
  unfold problem_103_spec.
  right.
  exists 3, "11".
  split; [lia|].
  split; [reflexivity|].
  split.
  - apply tbr_pos.
    apply tbp_xI.
    apply tbp_xO.
    apply tbp_xH.
  - reflexivity.
Qed.