Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition add_elements_spec (arr : list Z) (k : Z) (result : Z) : Prop :=
  let is_two_digits (x : Z) : bool := Z.ltb (Z.abs x) 100 in
  result = fold_right Z.add 0 (filter is_two_digits (firstn (Z.to_nat k) arr)).

Example test_add_elements:
  add_elements_spec [1000; 20; 300; 40000; 100; 500; 10000; 6000; 80; 800; 6000; 10000] 5 20.
Proof.
  unfold add_elements_spec.
  (* Simplify the expression:
     1. Z.to_nat 5 becomes 5%nat.
     2. firstn 5 [...] takes the first 5 elements: [1000; 20; 300; 40000; 100].
     3. filter checks if abs(x) < 100.
        abs(1000) = 1000 >= 100 (false).
        abs(20) = 20 < 100 (true).
        abs(300) = 300 >= 100 (false).
        abs(40000) = 40000 >= 100 (false).
        abs(100) = 100 >= 100 (false).
     4. The list becomes [20].
     5. fold_right sums them: 20 + 0 = 20.
  *)
  simpl.
  reflexivity.
Qed.