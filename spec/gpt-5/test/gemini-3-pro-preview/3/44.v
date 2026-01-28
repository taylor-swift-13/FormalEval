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

Example test_below_zero_1 : below_zero_spec [-8; -20; 30; -40; 50; -60] true.
Proof.
  unfold below_zero_spec.
  split.
  - split.
    + intro.
      exists [-8], [-20; 30; -40; 50; -60].
      split.
      * reflexivity.
      * unfold sum_list. simpl. lia.
    + intro. reflexivity.
  - split.
    + intro H. discriminate H.
    + intro H.
      specialize (H [-8] [-20; 30; -40; 50; -60] eq_refl).
      unfold sum_list in H. simpl in H. lia.
Qed.