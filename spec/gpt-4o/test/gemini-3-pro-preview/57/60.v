Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Definition monotonic_spec (l : list Z) (result : bool) : Prop :=
  result = true <-> 
    (forall i j, (i < j /\ j < length l)%nat -> nth i l 0 <= nth j l 0) \/
    (forall i j, (i < j /\ j < length l)%nat -> nth i l 0 >= nth j l 0).

Example test_monotonic_neg7_neg10_neg11 : monotonic_spec [-7; -10; -11] true.
Proof.
  unfold monotonic_spec.
  split.
  - intros _.
    right.
    intros i j H.
    simpl in H.
    destruct i as [|i].
    + destruct j as [|j]; [lia|].
      destruct j as [|j].
      * simpl. lia.
      * destruct j as [|j]; [simpl; lia|].
        lia.
    + destruct i as [|i].
      * destruct j as [|j]; [lia|].
        destruct j as [|j]; [lia|].
        destruct j as [|j].
        -- simpl. lia.
        -- lia.
      * lia.
  - intros _.
    reflexivity.
Qed.