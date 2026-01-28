Require Import List.
Require Import ZArith.

Open Scope Z_scope.

Definition double_the_difference_spec (lst : list Z) (result : Z) : Prop :=
  result = fold_left (fun acc num =>
    if (Z.odd num && (0 <? num))%bool then acc + num * num else acc) lst 0.

Example test_double_the_difference : double_the_difference_spec (-10 :: -20 :: -30 :: nil) 0.
Proof.
  (* Unfold the specification definition *)
  unfold double_the_difference_spec.
  
  (* Simplify the fold_left operation on the list *)
  simpl.
  
  (* Verify that 0 = 0 *)
  reflexivity.
Qed.