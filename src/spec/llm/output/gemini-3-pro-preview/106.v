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

Example test_case_1 : f_spec 5 [1; 2; 6; 24; 15].
Proof.
  unfold f_spec.
  split.
  - (* Verify length *)
    simpl. reflexivity.
  - (* Verify each element *)
    intros i Hi.
    (* Manually destruct i for values 0 to 4 *)
    destruct i as [|i].
    + (* i = 0 *) simpl. reflexivity.
    + destruct i as [|i].
      * (* i = 1 *) simpl. reflexivity.
      * destruct i as [|i].
        -- (* i = 2 *) simpl. reflexivity.
        -- destruct i as [|i].
           ++ (* i = 3 *) simpl. reflexivity.
           ++ destruct i as [|i].
              ** (* i = 4 *) simpl. reflexivity.
              ** (* i >= 5, contradiction with Hi: i < 5 *)
                 (* Use top-level lt_S_n from Arith/Peano instead of Nat.lt_S_n *)
                 do 5 apply lt_S_n in Hi.
                 inversion Hi.
Qed.