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

Example test_below_zero_complex : below_zero_spec [5%Z; -20%Z; 25%Z; -30%Z; 35%Z; -40%Z; 45%Z; -50%Z; -21%Z; -6%Z] true.
Proof.
  unfold below_zero_spec.
  split.
  - (* Case: result = true <-> ... *)
    split.
    + (* true = true -> exists ... *)
      intros _.
      exists [5%Z; -20%Z].
      exists [25%Z; -30%Z; 35%Z; -40%Z; 45%Z; -50%Z; -21%Z; -6%Z].
      split.
      * reflexivity.
      * unfold sum_list. simpl. lia.
    + (* exists ... -> true = true *)
      intros _. reflexivity.
  - (* Case: result = false <-> ... *)
    split.
    + (* true = false -> ... *)
      intro H. discriminate H.
    + (* forall ... -> true = false *)
      intro H.
      specialize (H [5%Z; -20%Z] [25%Z; -30%Z; 35%Z; -40%Z; 45%Z; -50%Z; -21%Z; -6%Z]).
      assert (Heq: [5%Z; -20%Z; 25%Z; -30%Z; 35%Z; -40%Z; 45%Z; -50%Z; -21%Z; -6%Z] = [5%Z; -20%Z] ++ [25%Z; -30%Z; 35%Z; -40%Z; 45%Z; -50%Z; -21%Z; -6%Z]).
      { reflexivity. }
      apply H in Heq.
      unfold sum_list in Heq. simpl in Heq.
      lia.
Qed.