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

Example test_below_zero_1 : below_zero_spec [1%Z; -2%Z; 3%Z; -4%Z; 4%Z; -6%Z; 7%Z; -8%Z; 9%Z; -10%Z; -8%Z] true.
Proof.
  unfold below_zero_spec.
  split.
  - split; [intros _|reflexivity].
    exists [1; -2].
    exists [3; -4; 4; -6; 7; -8; 9; -10; -8].
    split.
    + reflexivity.
    + unfold sum_list. simpl. lia.
  - split; [intro H; discriminate H|intro H].
    specialize (H [1; -2] [3; -4; 4; -6; 7; -8; 9; -10; -8] eq_refl).
    unfold sum_list in H. simpl in H. lia.
Qed.