Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.

Import ListNotations.
Open Scope Z_scope.

Definition Z_of_digit (c : ascii) : Z :=
  Z.of_nat (Ascii.nat_of_ascii c - Ascii.nat_of_ascii "0"%char).

Definition problem_44_pre (x : Z) (base : Z) : Prop := (base >= 2) /\ (base < 10).

Definition problem_44_spec (x : Z) (base : Z) (output : list ascii) : Prop :=
  let digits := List.map Z_of_digit output in
  (Forall (fun d => d < base) digits) /\
  (fold_left (fun acc d => acc * base + d) digits 0 = x).

Example test_case_123456789_3 : 
  problem_44_spec 123456789 3 
  ["2"%char; "2"%char; "1"%char; "2"%char; "1"%char; "0"%char; 
   "2"%char; "2"%char; "0"%char; "2"%char; "0"%char; "2"%char; 
   "1"%char; "2"%char; "2"%char; "0"%char; "0"%char].
Proof.
  unfold problem_44_spec.
  split.
  - vm_compute.
    repeat constructor.
  - vm_compute.
    reflexivity.
Qed.