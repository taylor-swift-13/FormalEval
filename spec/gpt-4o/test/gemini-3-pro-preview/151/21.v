Require Import List.
Import ListNotations.
Require Import ZArith.

Open Scope Z_scope.

Definition double_the_difference_spec (lst : list Z) (result : Z) : Prop :=
  result = fold_left (fun acc num =>
    if (Z.odd num && (0 <? num))%bool then acc + num * num else acc) lst 0.

Example test_double_the_difference : double_the_difference_spec [2; 4; 5; 8] 25.
Proof.
  unfold double_the_difference_spec.
  simpl.
  reflexivity.
Qed.