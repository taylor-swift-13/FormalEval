Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.micromega.Lia.
Import ListNotations.

Definition monotonic_spec (l : list nat) (result : bool) : Prop :=
  result = true <-> 
    (forall i j, i < j < length l -> nth i l 0 <= nth j l 0) \/
    (forall i j, i < j < length l -> nth i l 0 >= nth j l 0).

Example test_monotonic_4_1_1_0 : monotonic_spec [4; 1; 1; 0] true.
Proof.
  unfold monotonic_spec.
  split.
  - intros _.
    right.
    intros i j H.
    simpl in H.
    destruct i as [|i].
    + (* i = 0 *)
      simpl.
      destruct j as [|j]; [lia|].
      destruct j as [|j]; [simpl; lia|].
      destruct j as [|j]; [simpl; lia|].
      destruct j as [|j]; [simpl; lia|].
      lia.
    + destruct i as [|i].
      * (* i = 1 *)
        simpl.
        destruct j as [|j]; [lia|].
        destruct j as [|j]; [lia|].
        destruct j as [|j]; [simpl; lia|].
        destruct j as [|j]; [simpl; lia|].
        lia.
      * destruct i as [|i].
        -- (* i = 2 *)
           simpl.
           destruct j as [|j]; [lia|].
           destruct j as [|j]; [lia|].
           destruct j as [|j]; [lia|].
           destruct j as [|j]; [simpl; lia|].
           lia.
        -- (* i >= 3 *)
           lia.
  - intros _.
    reflexivity.
Qed.