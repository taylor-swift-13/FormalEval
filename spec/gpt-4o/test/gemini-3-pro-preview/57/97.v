Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Definition monotonic_spec (l : list Z) (result : bool) : Prop :=
  result = true <-> 
    (forall i j : nat, (i < j < length l)%nat -> nth i l 0 <= nth j l 0) \/
    (forall i j : nat, (i < j < length l)%nat -> nth i l 0 >= nth j l 0).

Example test_monotonic_new : monotonic_spec [2; -7; -11; -11] true.
Proof.
  unfold monotonic_spec.
  split.
  - intros _.
    right.
    intros i j H.
    assert (Hlen: length [2; -7; -11; -11] = 4%nat) by reflexivity.
    rewrite Hlen in H.
    destruct i as [|i].
    + simpl.
      destruct j as [|j]; [lia|].
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
        lia.
      * destruct i as [|i].
        -- simpl.
           destruct j as [|j]; [lia|].
           destruct j as [|j]; [lia|].
           destruct j as [|j]; [lia|].
           destruct j as [|j]; [simpl; lia|].
           lia.
        -- lia.
  - intros _. reflexivity.
Qed.