Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.

Import ListNotations.

Definition nat_of_digit (c : ascii) : nat :=
  Ascii.nat_of_ascii c - Ascii.nat_of_ascii "0"%char.

Definition problem_44_pre (x : nat) (base : nat) : Prop := (base >= 2)%nat /\ (base < 10)%nat.

Definition problem_44_spec (x : nat) (base : nat) (output : list ascii) : Prop :=
  let digits := List.map nat_of_digit output in
  (Forall (fun d => d < base) digits) /\
  (fold_left (fun acc d => acc * base + d) digits 0 = x).

Example test_case_9999999_9 : problem_44_spec 9999999 9 ["2"%char; "0"%char; "7"%char; "3"%char; "1"%char; "3"%char; "7"%char; "0"%char].
Proof.
  unfold problem_44_spec.
  split.
  - vm_compute.
    repeat constructor.
  - apply Nat.eqb_eq.
    vm_compute.
    reflexivity.
Qed.