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

Example test_below_zero : below_zero_spec [1; -1; 1; -1; 1; 1; -1; -1; -6; -1]%Z true.
Proof.
  unfold below_zero_spec.
  split.
  - split.
    + intros _.
      exists [1; -1; 1; -1; 1; 1; -1; -1; -6]%Z.
      exists [-1]%Z.
      split.
      * reflexivity.
      * unfold sum_list. simpl. lia.
    + intros _. reflexivity.
  - split.
    + intro H. discriminate H.
    + intro H.
      assert (H_contr : 0 <= sum_list [1; -1; 1; -1; 1; 1; -1; -1; -6]%Z).
      { apply H with (suffix := [-1]%Z). reflexivity. }
      unfold sum_list in H_contr. simpl in H_contr. lia.
Qed.