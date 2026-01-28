Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Definition triples_sum_to_zero_spec (l : list Z) (res : bool) : Prop :=
  res = true <->
  (exists i j k : nat,
    (i < length l)%nat /\ (j < length l)%nat /\ (k < length l)%nat /\
    i <> j /\ i <> k /\ j <> k /\
    nth i l 0 + nth j l 0 + nth k l 0 = 0).

Example test_triples_sum_to_zero : triples_sum_to_zero_spec [1; 3; 4; -11; 5; 6; 7; -15; 14; 9; 10; -11; -12; -13; -14; -15; 7; 2; 14] true.
Proof.
  unfold triples_sum_to_zero_spec.
  split.
  - intros _.
    exists 2%nat, 3%nat, 6%nat.
    simpl.
    repeat split; try lia.
  - intros _. reflexivity.
Qed.