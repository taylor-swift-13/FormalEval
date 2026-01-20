Require Import List.
Require Import ZArith.
Import ListNotations.

Open Scope Z_scope.

Definition abs_diff (a b : Z) : Z :=
  Z.abs (a - b).

Fixpoint compare_spec (game : list Z) (guess : list Z) (result : list Z) : Prop :=
  match game, guess, result with
  | [], [], [] => True
  | g :: gs, gu :: gus, r :: rs => r = abs_diff g gu /\ compare_spec gs gus rs
  | _, _, _ => False
  end.

Example test_compare_spec :
  compare_spec [90%Z; 30%Z; 21%Z; 50%Z] [90%Z; 30%Z; 21%Z; 50%Z] [0%Z; 0%Z; 0%Z; 0%Z].
Proof.
  unfold compare_spec.
  repeat split; unfold abs_diff; simpl; reflexivity.
Qed.