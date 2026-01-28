Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.micromega.Lia.
Import ListNotations.

Definition monotonic_spec (l : list nat) (result : bool) : Prop :=
  result = true <-> 
    (forall i j, i < j < length l -> nth i l 0 <= nth j l 0) \/
    (forall i j, i < j < length l -> nth i l 0 >= nth j l 0).

Example test_monotonic_5_4_3_3_3_2_1 : monotonic_spec [5; 4; 3; 3; 3; 2; 1] true.
Proof.
  unfold monotonic_spec.
  split.
  - intros _.
    right.
    intros i j H.
    simpl in H.
    do 7 (destruct i as [|i]; [
      simpl;
      do 8 (destruct j as [|j]; [ try lia | simpl; try lia ]);
      lia
    |]).
    lia.
  - intros _.
    reflexivity.
Qed.