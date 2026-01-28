Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition add_elements_spec (arr : list Z) (k : Z) (result : Z) : Prop :=
  let is_two_digits (x : Z) : bool := Z.ltb (Z.abs x) 100 in
  result = fold_right Z.add 0 (filter is_two_digits (firstn (Z.to_nat k) arr)).

Example test_add_elements:
  add_elements_spec [112; 555; 500; 100; 201; 300; 400] 2 0.
Proof.
  unfold add_elements_spec.
  (* Simplify the expression:
     1. Z.to_nat 2 becomes 2%nat.
     2. firstn 2 [...] takes the first 2 elements: [112; 555].
     3. filter checks if abs(x) < 100.
        abs(112)=112 < 100 (false).
        abs(555)=555 < 100 (false).
     4. The list becomes empty: [].
     5. fold_right sums them: 0.
  *)
  simpl.
  reflexivity.
Qed.