Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.micromega.Lia.
Import ListNotations.

Definition monotonic_spec (l : list nat) (result : bool) : Prop :=
  result = true <-> 
    (forall i j, i < j < length l -> nth i l 0 <= nth j l 0) \/
    (forall i j, i < j < length l -> nth i l 0 >= nth j l 0).

Example test_monotonic_10_9_8_7_7_7_7_7 : monotonic_spec [10; 9; 8; 7; 7; 7; 7; 7] true.
Proof.
  unfold monotonic_spec.
  split.
  - intros _.
    right.
    intros i j H.
    simpl in H.
    repeat (destruct i as [|i]; [| try lia]).
    all: repeat (destruct j as [|j]; [| try lia]).
    all: simpl; lia.
  - intros _.
    reflexivity.
Qed.