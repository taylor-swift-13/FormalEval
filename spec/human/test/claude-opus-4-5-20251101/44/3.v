Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Lia.

Import ListNotations.

Definition nat_of_digit (c : ascii) : nat :=
  Ascii.nat_of_ascii c - Ascii.nat_of_ascii "0"%char.

Definition problem_44_pre (x : nat) (base : nat) : Prop := (base >= 2)%nat /\ (base < 10)%nat.

Definition problem_44_spec (x : nat) (base : nat) (output : list ascii) : Prop :=
  let digits := List.map nat_of_digit output in
  (Forall (fun d => d < base) digits) /\
  (fold_left (fun acc d => acc * base + d) digits 0 = x).

Lemma nat_of_ascii_0 : Ascii.nat_of_ascii "0"%char = 48.
Proof. reflexivity. Qed.

Lemma nat_of_ascii_1 : Ascii.nat_of_ascii "1"%char = 49.
Proof. reflexivity. Qed.

Example test_change_base_234_2 : 
  problem_44_pre 234 2 /\ problem_44_spec 234 2 ["1"%char; "1"%char; "1"%char; "0"%char; "1"%char; "0"%char; "1"%char; "0"%char].
Proof.
  split.
  - unfold problem_44_pre. lia.
  - unfold problem_44_spec.
    split.
    + unfold nat_of_digit.
      simpl.
      repeat constructor; lia.
    + unfold nat_of_digit.
      simpl.
      reflexivity.
Qed.