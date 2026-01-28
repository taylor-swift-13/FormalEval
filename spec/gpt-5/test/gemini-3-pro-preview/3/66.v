Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Definition sum_list (l : list Z) : Z :=
  fold_left Z.add l 0%Z.

Definition below_zero_spec (operations : list Z) (result : bool) : Prop :=
  (result = true <-> exists prefix suffix, operations = prefix ++ suffix /\ sum_list prefix < 0%Z) /\
  (result = false <-> forall prefix suffix, operations = prefix ++ suffix -> 0%Z <= sum_list prefix).

Example test_below_zero : below_zero_spec [-8%Z; -20%Z; 30%Z; -40%Z; 50%Z; 40%Z] true.
Proof.
  unfold below_zero_spec.
  split.
  - split.
    + intros _.
      exists [-8%Z].
      exists [-20%Z; 30%Z; -40%Z; 50%Z; 40%Z].
      split.
      * reflexivity.
      * unfold sum_list. simpl. lia.
    + intros _. reflexivity.
  - split.
    + intros H. discriminate H.
    + intros H.
      specialize (H [-8%Z] [-20%Z; 30%Z; -40%Z; 50%Z; 40%Z]).
      assert (Heq : [-8%Z; -20%Z; 30%Z; -40%Z; 50%Z; 40%Z] = [-8%Z] ++ [-20%Z; 30%Z; -40%Z; 50%Z; 40%Z]).
      { reflexivity. }
      apply H in Heq.
      unfold sum_list in Heq. simpl in Heq. lia.
Qed.