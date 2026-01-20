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
  compare_spec [13%Z; 23%Z; 9%Z; 17%Z; 25%Z] [11%Z; 20%Z; 10%Z; 14%Z; 23%Z] [2%Z; 3%Z; 1%Z; 3%Z; 2%Z].
Proof.
  unfold compare_spec.
  repeat split; unfold abs_diff; simpl; reflexivity.
Qed.