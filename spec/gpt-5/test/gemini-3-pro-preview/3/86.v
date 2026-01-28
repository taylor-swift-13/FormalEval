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

Example test_below_zero_true : below_zero_spec [15%Z; 2%Z; -6%Z; -6%Z; -6%Z] true.
Proof.
  unfold below_zero_spec.
  split.
  - split.
    + intros _.
      exists [15%Z; 2%Z; -6%Z; -6%Z; -6%Z], [].
      split.
      * rewrite app_nil_r. reflexivity.
      * unfold sum_list. simpl. lia.
    + intros _. reflexivity.
  - split.
    + intros H. discriminate.
    + intros H.
      specialize (H [15%Z; 2%Z; -6%Z; -6%Z; -6%Z] []).
      rewrite app_nil_r in H.
      specialize (H eq_refl).
      unfold sum_list in H.
      simpl in H.
      lia.
Qed.