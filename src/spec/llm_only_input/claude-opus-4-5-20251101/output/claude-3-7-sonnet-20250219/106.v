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

Example test_f_spec : f_spec 5 [1; 2; 6; 24; 15].
Proof.
  unfold f_spec.
  split.
  - simpl. reflexivity.
  - intros i Hi.
    destruct i as [|i'].
    + lia.
    + destruct i' as [|i''].
      * simpl. reflexivity.
      * destruct i'' as [|i'''].
        -- simpl. reflexivity.
        -- destruct i''' as [|i''''].
           ++ simpl. reflexivity.
           ++ destruct i'''' as [|i'''''].
              ** simpl. reflexivity.
              ** destruct i''''' as [|i''''''].
                 --- simpl. reflexivity.
                 --- lia.
Qed.