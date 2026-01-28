Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition add_elements_spec (arr : list Z) (k : Z) (result : Z) : Prop :=
  let is_two_digits (x : Z) : bool := Z.ltb (Z.abs x) 100 in
  result = fold_right Z.add 0 (filter is_two_digits (firstn (Z.to_nat k) arr)).

Example test_add_elements:
  add_elements_spec [1; -2; -3; 41; 57; 76; 87; 88; 99] 3 (-4).
Proof.
  unfold add_elements_spec.
  (* Simplify the expression:
     1. Z.to_nat 3 becomes 3%nat.
     2. firstn 3 [...] takes the first 3 elements: [1; -2; -3].
     3. filter checks if abs(x) < 100. 
        abs(1)=1 < 100 (true), abs(-2)=2 < 100 (true), abs(-3)=3 < 100 (true).
     4. The list remains [1; -2; -3].
     5. fold_right sums them: 1 + (-2) + (-3) + 0 = -4.
  *)
  simpl.
  reflexivity.
Qed.