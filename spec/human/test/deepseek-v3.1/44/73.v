Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Lia.

Import ListNotations.

Definition nat_of_digit (c : ascii) : nat :=
  Ascii.nat_of_ascii c - Ascii.nat_of_ascii "0"%char.

Definition problem_44_pre (x : nat) (base : nat) : Prop := 
  (base >= 2)%nat /\ (base < 10)%nat.

Definition problem_44_spec (x : nat) (base : nat) (output : list ascii) : Prop :=
  let digits := List.map nat_of_digit output in
  (Forall (fun d => d < base) digits) /\
  (fold_left (fun acc d => acc * base + d) digits 0 = x).

Example test_change_base_5_3 : problem_44_spec 3 5 [Ascii.ascii_of_nat 51].
Proof.
  unfold problem_44_spec.
  simpl.
  split.
  - apply Forall_cons.
    + unfold nat_of_digit.
      simpl.
      lia.
    + apply Forall_nil.
  - simpl.
    reflexivity.
Qed.