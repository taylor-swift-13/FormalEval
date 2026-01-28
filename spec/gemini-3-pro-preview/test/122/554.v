Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition add_elements_spec (arr : list Z) (k : Z) (result : Z) : Prop :=
  let is_two_digits (x : Z) : bool := Z.ltb (Z.abs x) 100 in
  result = fold_right Z.add 0 (filter is_two_digits (firstn (Z.to_nat k) arr)).

Example test_add_elements:
  add_elements_spec [111; 1111; 22; 7; 444; 555; 80; 777; 888; 5050; 1000; 2000; 8000; 4039; 5050; 23; 1000000; 7000; 8000; 9000] 13 109.
Proof.
  unfold add_elements_spec.
  simpl.
  reflexivity.
Qed.