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

Example test_below_zero : below_zero_spec [1%Z; 2%Z; 3%Z; 4%Z; -10%Z; 5%Z; 6%Z; -15%Z; 3%Z] true.
Proof.
  unfold below_zero_spec.
  split.
  - split.
    + intros _.
      exists [1; 2; 3; 4; -10; 5; 6; -15].
      exists [3].
      split.
      * reflexivity.
      * unfold sum_list. simpl. lia.
    + intros _. reflexivity.
  - split.
    + intros H. discriminate H.
    + intros H.
      specialize (H [1; 2; 3; 4; -10; 5; 6; -15] [3]).
      assert (Heq: [1; 2; 3; 4; -10; 5; 6; -15; 3] = [1; 2; 3; 4; -10; 5; 6; -15] ++ [3]) by reflexivity.
      apply H in Heq.
      unfold sum_list in Heq. simpl in Heq.
      lia.
Qed.