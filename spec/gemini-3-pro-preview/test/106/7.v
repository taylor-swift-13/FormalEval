Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Init.Nat.
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

Example test_case_1 : f_spec 4 [1; 2; 6; 24].
Proof.
  unfold f_spec.
  split.
  - (* Verify length *)
    simpl. reflexivity.
  - (* Verify each element *)
    intros i Hi.
    destruct i as [|i].
    + (* i = 0 *) simpl. reflexivity.
    + destruct i as [|i].
      * (* i = 1 *) simpl. reflexivity.
      * destruct i as [|i].
        -- (* i = 2 *) simpl. reflexivity.
        -- destruct i as [|i].
           ++ (* i = 3 *) simpl. reflexivity.
           ++ (* i >= 4, contradiction with Hi: i < 4 *)
              do 4 apply lt_S_n in Hi.
              inversion Hi.
Qed.