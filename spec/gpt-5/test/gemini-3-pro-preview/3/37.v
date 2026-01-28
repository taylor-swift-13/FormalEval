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

Example test_below_zero_true : below_zero_spec [1%Z; 2%Z; 3%Z; 4%Z; -10%Z; 5%Z; 6%Z; -15%Z; -10%Z; 3%Z; 3%Z] true.
Proof.
  unfold below_zero_spec.
  split.
  - split.
    + intro.
      exists [1%Z; 2%Z; 3%Z; 4%Z; -10%Z; 5%Z; 6%Z; -15%Z], [-10%Z; 3%Z; 3%Z].
      split.
      * reflexivity.
      * unfold sum_list. simpl. lia.
    + intro. reflexivity.
  - split.
    + intro H. discriminate H.
    + intro H.
      specialize (H [1%Z; 2%Z; 3%Z; 4%Z; -10%Z; 5%Z; 6%Z; -15%Z] [-10%Z; 3%Z; 3%Z] eq_refl).
      unfold sum_list in H. simpl in H.
      lia.
Qed.