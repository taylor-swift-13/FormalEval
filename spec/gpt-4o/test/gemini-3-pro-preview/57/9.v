Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.micromega.Lia.
Import ListNotations.

Definition monotonic_spec (l : list nat) (result : bool) : Prop :=
  result = true <-> 
    (forall i j, i < j < length l -> nth i l 0 <= nth j l 0) \/
    (forall i j, i < j < length l -> nth i l 0 >= nth j l 0).

Example test_monotonic_10_9_8_7_6 : monotonic_spec [10; 9; 8; 7; 6] true.
Proof.
  unfold monotonic_spec.
  split.
  - intros _.
    right.
    intros i j H.
    simpl in H.
    (* We perform case analysis on index i. 
       Since i < j < 5, i can only be 0, 1, 2, or 3. *)
    destruct i as [|i].
    + (* i = 0 *)
      simpl.
      destruct j as [|j]; [lia|].
      destruct j as [|j]; [simpl; lia|].
      destruct j as [|j]; [simpl; lia|].
      destruct j as [|j]; [simpl; lia|].
      destruct j as [|j]; [simpl; lia|].
      lia. (* j >= 5 out of bounds *)
    + (* i > 0 *)
      destruct i as [|i].
      * (* i = 1 *)
        simpl.
        destruct j as [|j]; [lia|].
        destruct j as [|j]; [lia|].
        destruct j as [|j]; [simpl; lia|].
        destruct j as [|j]; [simpl; lia|].
        destruct j as [|j]; [simpl; lia|].
        lia. (* j >= 5 out of bounds *)
      * (* i > 1 *)
        destruct i as [|i].
        -- (* i = 2 *)
           simpl.
           destruct j as [|j]; [lia|].
           destruct j as [|j]; [lia|].
           destruct j as [|j]; [lia|].
           destruct j as [|j]; [simpl; lia|].
           destruct j as [|j]; [simpl; lia|].
           lia. (* j >= 5 out of bounds *)
        -- (* i > 2 *)
           destruct i as [|i].
           ++ (* i = 3 *)
              simpl.
              destruct j as [|j]; [lia|].
              destruct j as [|j]; [lia|].
              destruct j as [|j]; [lia|].
              destruct j as [|j]; [lia|].
              destruct j as [|j]; [simpl; lia|].
              lia. (* j >= 5 out of bounds *)
           ++ (* i >= 4 *)
              (* If i >= 4, then i < j < 5 is impossible *)
              lia.
  - intros _.
    reflexivity.
Qed.