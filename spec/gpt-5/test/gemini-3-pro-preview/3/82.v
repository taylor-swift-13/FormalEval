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

Example test_below_zero_1 : below_zero_spec [-2; 0; -2] true.
Proof.
  unfold below_zero_spec.
  split.
  - split.
    + intros _.
      exists [-2], [0; -2].
      split.
      * reflexivity.
      * unfold sum_list. simpl. lia.
    + intros _. reflexivity.
  - split.
    + intros H. discriminate H.
    + intros H.
      assert (Heq: [-2; 0; -2] = [-2] ++ [0; -2]).
      { reflexivity. }
      specialize (H [-2] [0; -2] Heq).
      unfold sum_list in H. simpl in H.
      lia.
Qed.