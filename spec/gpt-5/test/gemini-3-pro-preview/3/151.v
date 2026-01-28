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

Example test_below_zero_1 : below_zero_spec [1%Z; 2%Z; 3%Z; 4%Z; 5%Z; -15%Z; 6%Z; 8%Z; 8%Z; 9%Z; -19%Z; 21%Z; -19%Z; -19%Z] true.
Proof.
  unfold below_zero_spec.
  split.
  - split; intro H.
    + exists [1%Z; 2%Z; 3%Z; 4%Z; 5%Z; -15%Z; 6%Z; 8%Z; 8%Z; 9%Z; -19%Z; 21%Z; -19%Z; -19%Z], [].
      split.
      * reflexivity.
      * unfold sum_list. simpl. lia.
    + reflexivity.
  - split; intro H.
    + discriminate.
    + specialize (H [1%Z; 2%Z; 3%Z; 4%Z; 5%Z; -15%Z; 6%Z; 8%Z; 8%Z; 9%Z; -19%Z; 21%Z; -19%Z; -19%Z] []).
      assert (Heq : [1%Z; 2%Z; 3%Z; 4%Z; 5%Z; -15%Z; 6%Z; 8%Z; 8%Z; 9%Z; -19%Z; 21%Z; -19%Z; -19%Z] = [1%Z; 2%Z; 3%Z; 4%Z; 5%Z; -15%Z; 6%Z; 8%Z; 8%Z; 9%Z; -19%Z; 21%Z; -19%Z; -19%Z] ++ []).
      { reflexivity. }
      specialize (H Heq).
      unfold sum_list in H. simpl in H. lia.
Qed.