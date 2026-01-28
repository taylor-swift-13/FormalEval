Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Definition monotonic_spec (l : list Z) (result : bool) : Prop :=
  result = true <-> 
    (forall i j, (i < j /\ j < length l)%nat -> nth i l 0 <= nth j l 0) \/
    (forall i j, (i < j /\ j < length l)%nat -> nth i l 0 >= nth j l 0).

Example test_monotonic_neg_5_9_11 : monotonic_spec [-5; -9; -11] true.
Proof.
  unfold monotonic_spec.
  split.
  - intros _.
    right.
    intros i j H.
    destruct H as [H_lt H_bd].
    simpl in H_bd.
    (* Case analysis on index i *)
    destruct i as [|i].
    + (* i = 0 *)
      destruct j as [|j]; [lia|].
      destruct j as [|j].
      * (* j = 1 *)
        simpl. lia. (* -5 >= -9 *)
      * (* j > 1 *)
        destruct j as [|j].
        -- (* j = 2 *)
           simpl. lia. (* -5 >= -11 *)
        -- (* j >= 3 *)
           lia. (* Out of bounds *)
    + (* i > 0 *)
      destruct i as [|i].
      * (* i = 1 *)
        destruct j as [|j]; [lia|].
        destruct j as [|j]; [lia|].
        destruct j as [|j].
        -- (* j = 2 *)
           simpl. lia. (* -9 >= -11 *)
        -- (* j >= 3 *)
           lia. (* Out of bounds *)
      * (* i > 1 *)
        destruct i as [|i].
        -- (* i = 2 *)
           (* j must be > 2, so >= 3, out of bounds *)
           lia.
        -- (* i >= 3 *)
           lia.
  - intros _.
    reflexivity.
Qed.