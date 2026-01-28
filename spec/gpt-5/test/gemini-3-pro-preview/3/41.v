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

Example test_below_zero : below_zero_spec [10; -15; 20; -25; 30; -4; 40; -45; 40] true.
Proof.
  unfold below_zero_spec.
  split.
  - split.
    + intros _.
      exists [10; -15].
      exists [20; -25; 30; -4; 40; -45; 40].
      split.
      * reflexivity.
      * unfold sum_list. simpl. lia.
    + intros _. reflexivity.
  - split.
    + intros H. discriminate H.
    + intros H.
      exfalso.
      specialize (H [10; -15] [20; -25; 30; -4; 40; -45; 40]).
      assert (Heq : [10; -15; 20; -25; 30; -4; 40; -45; 40] = [10; -15] ++ [20; -25; 30; -4; 40; -45; 40]) by reflexivity.
      apply H in Heq.
      unfold sum_list in Heq. simpl in Heq. lia.
Qed.