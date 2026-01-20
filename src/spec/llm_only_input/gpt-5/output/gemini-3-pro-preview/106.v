Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Init.Nat.
Require Import Lia.
Import ListNotations.

Fixpoint factorial (n : nat) : nat :=
  match n with
  | 0 => 1
  | S p => n * factorial p
  end.

Fixpoint sum_1_to_n (n : nat) : nat :=
  match n with
  | 0 => 0
  | S p => n + sum_1_to_n p
  end.

Definition f_spec (n : nat) (result : list nat) : Prop :=
  length result = n /\
  (forall i : nat, i < n ->
    let logical_index := i + 1 in
    let val := nth i result 0 in
    if Nat.even logical_index then
      val = factorial logical_index
    else
      val = sum_1_to_n logical_index).

Example test_case_f_spec :
  f_spec 5 [1; 2; 6; 24; 15].
Proof.
  unfold f_spec.
  split.
  - simpl. reflexivity.
  - intros i Hi.
    destruct i as [|i1]; [simpl; reflexivity |].
    destruct i1 as [|i2]; [simpl; reflexivity |].
    destruct i2 as [|i3]; [simpl; reflexivity |].
    destruct i3 as [|i4]; [simpl; reflexivity |].
    destruct i4 as [|i5]; [simpl; reflexivity |].
    exfalso. lia.
Qed.