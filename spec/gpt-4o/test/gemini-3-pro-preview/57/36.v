Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.micromega.Lia.
Import ListNotations.

Definition monotonic_spec (l : list nat) (result : bool) : Prop :=
  result = true <-> 
    (forall i j, i < j < length l -> nth i l 0 <= nth j l 0) \/
    (forall i j, i < j < length l -> nth i l 0 >= nth j l 0).

Example test_monotonic_1 : monotonic_spec [1] true.
Proof.
  unfold monotonic_spec.
  split.
  - intros _.
    left.
    intros i j H.
    simpl in H.
    lia.
  - intros _.
    reflexivity.
Qed.