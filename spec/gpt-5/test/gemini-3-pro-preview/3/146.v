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

Example test_below_zero_true : below_zero_spec [100; -200; 300; -400; 500; -1000; 500] true.
Proof.
  unfold below_zero_spec.
  split.
  - split.
    + intros _.
      exists [100; -200], [300; -400; 500; -1000; 500].
      split.
      * reflexivity.
      * unfold sum_list. simpl. lia.
    + intros _. reflexivity.
  - split.
    + intros H. discriminate H.
    + intros H.
      assert (Heq: [100; -200; 300; -400; 500; -1000; 500] = [100; -200] ++ [300; -400; 500; -1000; 500]) by reflexivity.
      specialize (H [100; -200] [300; -400; 500; -1000; 500] Heq).
      unfold sum_list in H. simpl in H. lia.
Qed.