Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.micromega.Lia.
Import ListNotations.

Definition monotonic_spec (l : list nat) (result : bool) : Prop :=
  result = true <-> 
    (forall i j, i < j < length l -> nth i l 0 <= nth j l 0) \/
    (forall i j, i < j < length l -> nth i l 0 >= nth j l 0).

Example test_monotonic_10_9_8_7_7 : monotonic_spec [10; 9; 8; 7; 7] true.
Proof.
  unfold monotonic_spec.
  split.
  - intros _.
    right.
    intros i j H.
    simpl in H.
    destruct i as [|i].
    + simpl.
      destruct j as [|j]; [lia|].
      destruct j as [|j]; [simpl; lia|].
      destruct j as [|j]; [simpl; lia|].
      destruct j as [|j]; [simpl; lia|].
      destruct j as [|j]; [simpl; lia|].
      lia.
    + destruct i as [|i].
      * simpl.
        destruct j as [|j]; [lia|].
        destruct j as [|j]; [lia|].
        destruct j as [|j]; [simpl; lia|].
        destruct j as [|j]; [simpl; lia|].
        destruct j as [|j]; [simpl; lia|].
        lia.
      * destruct i as [|i].
        -- simpl.
           destruct j as [|j]; [lia|].
           destruct j as [|j]; [lia|].
           destruct j as [|j]; [lia|].
           destruct j as [|j]; [simpl; lia|].
           destruct j as [|j]; [simpl; lia|].
           lia.
        -- destruct i as [|i].
           ++ simpl.
              destruct j as [|j]; [lia|].
              destruct j as [|j]; [lia|].
              destruct j as [|j]; [lia|].
              destruct j as [|j]; [lia|].
              destruct j as [|j]; [simpl; lia|].
              lia.
           ++ lia.
  - intros _.
    reflexivity.
Qed.