Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Definition monotonic_spec (l : list Z) (result : bool) : Prop :=
  result = true <-> 
    (forall i j, (i < j < length l)%nat -> nth i l 0 <= nth j l 0) \/
    (forall i j, (i < j < length l)%nat -> nth i l 0 >= nth j l 0).

Example test_monotonic_neg_5_7_9_11 : monotonic_spec [-5; -7; -9; -11] true.
Proof.
  unfold monotonic_spec.
  split.
  - intros _.
    right.
    intros i j H.
    destruct i as [|i].
    + (* i = 0 *)
      destruct j as [|j]; [lia|].
      destruct j as [|j]; [simpl; lia|].
      destruct j as [|j]; [simpl; lia|].
      destruct j as [|j]; [simpl; lia|].
      simpl in H; lia.
    + (* i > 0 *)
      destruct i as [|i].
      * (* i = 1 *)
        destruct j as [|j]; [lia|].
        destruct j as [|j]; [lia|].
        destruct j as [|j]; [simpl; lia|].
        destruct j as [|j]; [simpl; lia|].
        simpl in H; lia.
      * (* i > 1 *)
        destruct i as [|i].
        -- (* i = 2 *)
           destruct j as [|j]; [lia|].
           destruct j as [|j]; [lia|].
           destruct j as [|j]; [lia|].
           destruct j as [|j]; [simpl; lia|].
           simpl in H; lia.
        -- (* i >= 3 *)
           simpl in H; lia.
  - intros _.
    reflexivity.
Qed.