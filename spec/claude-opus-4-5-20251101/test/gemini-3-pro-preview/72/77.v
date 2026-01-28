Require Import List.
Require Import ZArith.
Require Import Reals.
Require Import Psatz.
Require Import Lra.
Import ListNotations.

Open Scope R_scope.

Fixpoint sum_list (l : list R) : R :=
  match l with
  | [] => 0
  | x :: xs => x + sum_list xs
  end.

Definition is_palindrome (l : list R) : Prop :=
  l = rev l.

Definition will_it_fly_spec (q : list R) (w : Z) (result : bool) : Prop :=
  result = true <-> (is_palindrome q /\ sum_list q <= IZR w).

Example test_will_it_fly : will_it_fly_spec [48.77540799744989%R; -3.8838243003108204%R; -48.319352731351685%R] 2%Z false.
Proof.
  unfold will_it_fly_spec.
  split.
  - intros H. discriminate H.
  - intros [Hpal Hsum].
    unfold is_palindrome in Hpal.
    simpl in Hpal.
    injection Hpal as H1 H2.
    lra.
Qed.