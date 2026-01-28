Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.ZArith.ZArith.
Require Import Lia.
Import ListNotations.
Open Scope Z_scope.

Fixpoint factorial (k : nat) : Z :=
  match k with
  | 0%nat => 1
  | S k' => (Z.of_nat k) * factorial k'
  end.

Fixpoint sum_1_to_i (i : nat) : Z :=
  match i with
  | 0%nat => 0
  | S i' => (Z.of_nat i) + sum_1_to_i i'
  end.

Definition f_spec (n : nat) (l : list Z) : Prop :=
  length l = n /\
  (forall i, (1 <= i <= n)%nat ->
    nth (i-1)%nat l 0 = 
      if Nat.even i then factorial i else sum_1_to_i i).

Example test_case : f_spec 14 [1; 2; 6; 24; 15; 720; 28; 40320; 45; 3628800; 66; 479001600; 91; 87178291200].
Proof.
  unfold f_spec.
  split.
  - (* Check length *)
    simpl. reflexivity.
  - (* Check elements *)
    intros i [Hmin Hmax].
    destruct i. { lia. } (* 0 *)
    destruct i. { simpl. reflexivity. } (* 1 *)
    destruct i. { simpl. reflexivity. } (* 2 *)
    destruct i. { simpl. reflexivity. } (* 3 *)
    destruct i. { simpl. reflexivity. } (* 4 *)
    destruct i. { simpl. reflexivity. } (* 5 *)
    destruct i. { simpl. reflexivity. } (* 6 *)
    destruct i. { simpl. reflexivity. } (* 7 *)
    destruct i. { simpl. reflexivity. } (* 8 *)
    destruct i. { simpl. reflexivity. } (* 9 *)
    destruct i. { simpl. reflexivity. } (* 10 *)
    destruct i. { simpl. reflexivity. } (* 11 *)
    destruct i. { simpl. reflexivity. } (* 12 *)
    destruct i. { simpl. reflexivity. } (* 13 *)
    destruct i. { simpl. reflexivity. } (* 14 *)
    lia. (* > 14 *)
Qed.