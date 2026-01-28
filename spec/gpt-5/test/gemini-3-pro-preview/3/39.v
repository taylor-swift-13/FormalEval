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

Example test_below_zero_1 : below_zero_spec [-1; -2; -3; 6; 7]%Z true.
Proof.
  unfold below_zero_spec.
  split.
  - split.
    + intros _.
      exists [-1]%Z, [-2; -3; 6; 7]%Z.
      split.
      * reflexivity.
      * unfold sum_list. simpl. lia.
    + intros _. reflexivity.
  - split.
    + intros H. discriminate H.
    + intros H.
      specialize (H [-1]%Z [-2; -3; 6; 7]%Z).
      assert (Heq: [-1; -2; -3; 6; 7]%Z = [-1]%Z ++ [-2; -3; 6; 7]%Z) by reflexivity.
      apply H in Heq.
      unfold sum_list in Heq. simpl in Heq.
      lia.
Qed.