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

Example test_monotonic_complex : monotonic_spec [1; 2; 1; -7; 2; 1; 2; 1; 1; 1] false.
Proof.
  unfold monotonic_spec.
  split.
  - intros H. discriminate H.
  - intros [H_inc | H_dec].
    + (* Refute increasing assumption by showing l[1] > l[2] *)
      specialize (H_inc 1%nat 2%nat).
      assert (H_bounds : (1 < 2 < 10)%nat) by lia.
      apply H_inc in H_bounds.
      simpl in H_bounds.
      lia.
    + (* Refute decreasing assumption by showing l[0] < l[1] *)
      specialize (H_dec 0%nat 1%nat).
      assert (H_bounds : (0 < 1 < 10)%nat) by lia.
      apply H_dec in H_bounds.
      simpl in H_bounds.
      lia.
Qed.