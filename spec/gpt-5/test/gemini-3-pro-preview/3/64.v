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

Example test_below_zero : below_zero_spec [1%Z; 2%Z; 3%Z; 4%Z; -20%Z; 5%Z; 6%Z; -15%Z; 5%Z] true.
Proof.
  unfold below_zero_spec.
  split.
  - (* Case: result = true <-> ... *)
    split.
    + (* true = true -> exists ... *)
      intros _.
      exists [1%Z; 2%Z; 3%Z; 4%Z; -20%Z], [5%Z; 6%Z; -15%Z; 5%Z].
      split.
      * reflexivity.
      * unfold sum_list. simpl. lia.
    + (* exists ... -> true = true *)
      intro H. reflexivity.
  - (* Case: result = false <-> ... *)
    split.
    + (* true = false -> forall ... *)
      intro H. discriminate H.
    + (* forall ... -> true = false *)
      intros H.
      specialize (H [1%Z; 2%Z; 3%Z; 4%Z; -20%Z] [5%Z; 6%Z; -15%Z; 5%Z] eq_refl).
      unfold sum_list in H. simpl in H. lia.
Qed.