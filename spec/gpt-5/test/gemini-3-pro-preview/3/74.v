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

Example test_example : below_zero_spec [5%Z; 15%Z; -20%Z; 25%Z; -30%Z; -40%Z; 45%Z; -50%Z; -21%Z] true.
Proof.
  unfold below_zero_spec.
  split.
  - split.
    + intros _.
      exists [5%Z; 15%Z; -20%Z; 25%Z; -30%Z].
      exists [-40%Z; 45%Z; -50%Z; -21%Z].
      split.
      * reflexivity.
      * unfold sum_list. simpl. lia.
    + intros _. reflexivity.
  - split.
    + intro H. discriminate H.
    + intros H.
      specialize (H [5%Z; 15%Z; -20%Z; 25%Z; -30%Z] [-40%Z; 45%Z; -50%Z; -21%Z]).
      assert (Heq : [5%Z; 15%Z; -20%Z; 25%Z; -30%Z; -40%Z; 45%Z; -50%Z; -21%Z] = [5%Z; 15%Z; -20%Z; 25%Z; -30%Z] ++ [-40%Z; 45%Z; -50%Z; -21%Z]) by reflexivity.
      apply H in Heq.
      unfold sum_list in Heq. simpl in Heq.
      lia.
Qed.