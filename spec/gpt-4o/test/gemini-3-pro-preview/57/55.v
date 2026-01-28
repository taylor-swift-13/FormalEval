Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.micromega.Lia.
Import ListNotations.

Definition monotonic_spec (l : list nat) (result : bool) : Prop :=
  result = true <-> 
    (forall i j, i < j < length l -> nth i l 0 <= nth j l 0) \/
    (forall i j, i < j < length l -> nth i l 0 >= nth j l 0).

Example test_monotonic_1_2_2_7 : monotonic_spec [1; 2; 2; 7] true.
Proof.
  unfold monotonic_spec.
  split.
  - intros _.
    left.
    intros i j H.
    simpl in H.
    (* We perform case analysis on index i. 
       Since i < j < 4, i can only be 0, 1, or 2. *)
    destruct i as [|i].
    + (* i = 0 *)
      simpl.
      destruct j as [|j]; [lia|].
      destruct j as [|j]; [simpl; lia|].
      destruct j as [|j]; [simpl; lia|].
      destruct j as [|j]; [simpl; lia|].
      lia. (* j >= 4 out of bounds *)
    + (* i > 0 *)
      destruct i as [|i].
      * (* i = 1 *)
        simpl.
        destruct j as [|j]; [lia|].
        destruct j as [|j]; [lia|].
        destruct j as [|j]; [simpl; lia|].
        destruct j as [|j]; [simpl; lia|].
        lia. (* j >= 4 out of bounds *)
      * (* i > 1 *)
        destruct i as [|i].
        -- (* i = 2 *)
           simpl.
           destruct j as [|j]; [lia|].
           destruct j as [|j]; [lia|].
           destruct j as [|j]; [lia|].
           destruct j as [|j]; [simpl; lia|].
           lia. (* j >= 4 out of bounds *)
        -- (* i >= 3 *)
           (* If i >= 3, then i < j < 4 is impossible *)
           lia.
  - intros _.
    reflexivity.
Qed.