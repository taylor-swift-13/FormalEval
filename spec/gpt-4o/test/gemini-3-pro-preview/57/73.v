Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.micromega.Lia.
Import ListNotations.

Definition monotonic_spec (l : list nat) (result : bool) : Prop :=
  result = true <-> 
    (forall i j, i < j < length l -> nth i l 0 <= nth j l 0) \/
    (forall i j, i < j < length l -> nth i l 0 >= nth j l 0).

Example test_monotonic_1_8 : monotonic_spec [1; 8] true.
Proof.
  unfold monotonic_spec.
  split.
  - intros _.
    left.
    intros i j H.
    simpl in H.
    destruct i as [|i].
    + (* i = 0 *)
      simpl.
      destruct j as [|j]; [lia|].
      destruct j as [|j]; [simpl; lia|].
      lia. (* j >= 2 out of bounds *)
    + (* i > 0 *)
      destruct i as [|i].
      * (* i = 1 *)
        (* i < j < 2 is impossible for i = 1 *)
        lia.
      * (* i > 1 *)
        lia.
  - intros _.
    reflexivity.
Qed.