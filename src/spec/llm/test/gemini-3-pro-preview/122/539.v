Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition add_elements_spec (arr : list Z) (k : Z) (result : Z) : Prop :=
  let is_two_digits (x : Z) : bool := Z.ltb (Z.abs x) 100 in
  result = fold_right Z.add 0 (filter is_two_digits (firstn (Z.to_nat k) arr)).

Example test_add_elements:
  add_elements_spec [111; 1111; 22; 222; 333; 444; 555; 666; 777; 888; 999; 1000; 2000; 3030; 5050; 6000; 8000; 9000] 13 22.
Proof.
  unfold add_elements_spec.
  simpl.
  reflexivity.
Qed.