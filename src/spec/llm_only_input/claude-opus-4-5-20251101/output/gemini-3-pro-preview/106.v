Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Init.Nat.
Require Import Coq.micromega.Lia.
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

(* Verify the expected values:
   i=0: logical_index=1 (odd), sum_1_to_n(1)=1
   i=1: logical_index=2 (even), factorial(2)=2
   i=2: logical_index=3 (odd), sum_1_to_n(3)=3+2+1=6
   i=3: logical_index=4 (even), factorial(4)=24
   i=4: logical_index=5 (odd), sum_1_to_n(5)=5+4+3+2+1=15
   
   So the list should be [1; 2; 6; 24; 15] *)

Example test_f_spec : f_spec 5 [1; 2; 6; 24; 15].
Proof.
  unfold f_spec.
  split.
  - simpl. reflexivity.
  - intros i Hi.
    destruct i as [|i'].
    + (* i = 0, logical_index = 1, odd *)
      simpl. reflexivity.
    + destruct i' as [|i''].
      * (* i = 1, logical_index = 2, even *)
        simpl. reflexivity.
      * destruct i'' as [|i'''].
        -- (* i = 2, logical_index = 3, odd *)
           simpl. reflexivity.
        -- destruct i''' as [|i''''].
           ++ (* i = 3, logical_index = 4, even *)
              simpl. reflexivity.
           ++ destruct i'''' as [|i'''''].
              ** (* i = 4, logical_index = 5, odd *)
                 simpl. reflexivity.
              ** (* i >= 5, contradiction with Hi *)
                 simpl in Hi. lia.
Qed.