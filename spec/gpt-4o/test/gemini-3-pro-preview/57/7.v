Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.micromega.Lia.
Import ListNotations.

Definition monotonic_spec (l : list nat) (result : bool) : Prop :=
  result = true <-> 
    (forall i j, i < j < length l -> nth i l 0 <= nth j l 0) \/
    (forall i j, i < j < length l -> nth i l 0 >= nth j l 0).

Example test_monotonic_1_2_3_4_5_60 : monotonic_spec [1; 2; 3; 4; 5; 60] true.
Proof.
  unfold monotonic_spec.
  split.
  - intros _.
    left.
    intros i j H.
    simpl in H.
    destruct i as [|i].
    + (* i = 0 *)
      destruct j as [|j]; [lia|].
      destruct j as [|j]; [simpl; lia|].
      destruct j as [|j]; [simpl; lia|].
      destruct j as [|j]; [simpl; lia|].
      destruct j as [|j]; [simpl; lia|].
      destruct j as [|j]; [simpl; lia|].
      lia.
    + (* i > 0 *)
      destruct i as [|i].
      * (* i = 1 *)
        destruct j as [|j]; [lia|].
        destruct j as [|j]; [lia|].
        destruct j as [|j]; [simpl; lia|].
        destruct j as [|j]; [simpl; lia|].
        destruct j as [|j]; [simpl; lia|].
        destruct j as [|j]; [simpl; lia|].
        lia.
      * (* i > 1 *)
        destruct i as [|i].
        -- (* i = 2 *)
           destruct j as [|j]; [lia|].
           destruct j as [|j]; [lia|].
           destruct j as [|j]; [lia|].
           destruct j as [|j]; [simpl; lia|].
           destruct j as [|j]; [simpl; lia|].
           destruct j as [|j]; [simpl; lia|].
           lia.
        -- (* i > 2 *)
           destruct i as [|i].
           ++ (* i = 3 *)
              destruct j as [|j]; [lia|].
              destruct j as [|j]; [lia|].
              destruct j as [|j]; [lia|].
              destruct j as [|j]; [lia|].
              destruct j as [|j]; [simpl; lia|].
              destruct j as [|j]; [simpl; lia|].
              lia.
           ++ (* i > 3 *)
              destruct i as [|i].
              ** (* i = 4 *)
                 destruct j as [|j]; [lia|].
                 destruct j as [|j]; [lia|].
                 destruct j as [|j]; [lia|].
                 destruct j as [|j]; [lia|].
                 destruct j as [|j]; [lia|].
                 destruct j as [|j]; [simpl; lia|].
                 lia.
              ** (* i >= 5 *)
                 lia.
  - intros _.
    reflexivity.
Qed.