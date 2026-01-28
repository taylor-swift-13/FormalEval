Require Import Coq.Reals.Rdefinitions.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.Even.
Import ListNotations.

Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Require Import Coq.micromega.Lia.

Open Scope R_scope.

Fixpoint eval_poly (coeffs : list R) (x : R) : R :=
  match coeffs with
  | [] => 0%R
  | c :: cs => (c + x * (eval_poly cs x))%R
  end.

Definition problem_32_pre (input : list R) : Prop :=
  Nat.lt 0 (length input) /\ Nat.Even (length input).

Definition problem_32_spec (input : list R) (output : R) : Prop :=
  eval_poly input output = 0%R.

Example problem_32_test :
  problem_32_pre [-10%R; -2%R] /\
  problem_32_spec [-10%R; -2%R] (-5%R).
Proof.
  unfold problem_32_pre, problem_32_spec.
  split.
  - simpl. split.
    + lia.
    + exists 1%nat. simpl. reflexivity.
  - simpl. lra.
Qed.