Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Lia.
Import ListNotations.

Fixpoint factorial (k : nat) : nat :=
  match k with
  | 0 => 1
  | S k' => (S k') * factorial k'
  end.

Fixpoint sum_1_to_i (i : nat) : nat :=
  match i with
  | 0 => 0
  | S i' => i + sum_1_to_i i'
  end.

Definition f_spec (n : nat) (l : list nat) : Prop :=
  length l = n /\
  (forall i, 1 <= i <= n ->
    nth (i-1) l 0 = 
      if Nat.even i then factorial i else sum_1_to_i i).

Example test_case : f_spec 4 [1; 2; 6; 24].
Proof.
  unfold f_spec.
  split.
  - simpl. reflexivity.
  - intros i [Hmin Hmax].
    destruct i.
    + lia.
    + destruct i.
      * simpl. reflexivity.
      * destruct i.
        -- simpl. reflexivity.
        -- destruct i.
           ++ simpl. reflexivity.
           ++ destruct i.
              ** simpl. reflexivity.
              ** lia.
Qed.