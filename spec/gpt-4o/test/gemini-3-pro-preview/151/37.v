Require Import List.
Require Import ZArith.
Import ListNotations.

Open Scope Z_scope.

Definition double_the_difference_spec (lst : list Z) (result : Z) : Prop :=
  result = fold_left (fun acc num =>
    if (Z.odd num && (0 <? num))%bool then acc + num * num else acc) lst 0.

Example test_double_the_difference : double_the_difference_spec [3%Z; 5%Z; 7%Z; 3%Z] 92%Z.
Proof.
  unfold double_the_difference_spec.
  simpl.
  reflexivity.
Qed.