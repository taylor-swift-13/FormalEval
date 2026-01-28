Require Import ZArith.
Require Import String.
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
  | tbr_zero : to_binary_rel 0 "0b0"
  | tbr_pos : forall p s, to_binary_p_rel p s -> to_binary_rel (Z.pos p) ("0b" ++ s)
  | tbr_neg : forall p, to_binary_rel (Z.neg p) "Error: Negative numbers not supported".

Definition problem_103_pre (n m : Z) : Prop := n > 0 /\ m > 0.

Definition problem_103_spec (n m : Z) (output : result) : Prop :=
  (n > m /\ output = NegativeOne) \/
  (exists sum count rounded_avg bin_str,
     n <= m /\
     rounded_avg = (n + m) / 2 /\
     to_binary_rel rounded_avg bin_str /\
     output = Binary bin_str).

(* Helper lemma: to_binary_p_rel 3 "11" *)

(* Recall: 3 = xI (xI xH) *)
Lemma to_binary_p_3 : to_binary_p_rel 3 "11".
Proof.
  (* 3 = 2*1 + 1 *)
  apply tbp_xI.
  apply tbp_xI.
  apply tbp_xH.
Qed.

Lemma to_binary_rel_3 : to_binary_rel 3 "0b11".
Proof.
  apply tbr_pos with (p := 3).
  apply to_binary_p_3.
Qed.

Example test_rounded_avg_1_5 :
  problem_103_pre 1 5 /\
  problem_103_spec 1 5 (Binary "0b11").
Proof.
  split.
  - (* Precondition: n=1>0 and m=5>0 *)
    lia.
  - (* Spec *)
    unfold problem_103_spec.
    right.
    exists (1 + 5).
    exists 2.
    exists ((1 + 5) / 2).
    exists "0b11".
    repeat split.
    + lia.
    + reflexivity.
    + apply to_binary_rel_3.
    + reflexivity.
Qed.