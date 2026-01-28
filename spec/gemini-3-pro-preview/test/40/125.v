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

Example test_triples_sum_to_zero : triples_sum_to_zero_spec [10%Z; 20%Z; 30%Z; -40%Z; -50%Z; -60%Z; -70%Z; -80%Z; -90%Z; 100%Z; 200%Z; 300%Z; -400%Z; -500%Z; -600%Z; 700%Z; -800%Z; -900%Z; -3%Z; 1000%Z; -50%Z; 75%Z] true.
Proof.
  unfold triples_sum_to_zero_spec.
  split.
  - intros _.
    exists 0%nat, 2%nat, 3%nat.
    repeat split; try (simpl; lia).
  - intros _. reflexivity.
Qed.