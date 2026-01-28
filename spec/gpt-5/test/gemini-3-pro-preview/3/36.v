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

Example test_below_zero_true : below_zero_spec [2; 3; 4; -10; 5; 6; -15; -6] true.
Proof.
  unfold below_zero_spec.
  split.
  - split; intro H.
    + exists [2; 3; 4; -10], [5; 6; -15; -6].
      split.
      * reflexivity.
      * unfold sum_list. simpl. lia.
    + reflexivity.
  - split; intro H.
    + discriminate.
    + specialize (H [2; 3; 4; -10] [5; 6; -15; -6]).
      assert (Heq: [2; 3; 4; -10; 5; 6; -15; -6] = [2; 3; 4; -10] ++ [5; 6; -15; -6]) by reflexivity.
      apply H in Heq.
      unfold sum_list in Heq. simpl in Heq. lia.
Qed.