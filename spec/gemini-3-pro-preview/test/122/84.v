Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition add_elements_spec (arr : list Z) (k : Z) (result : Z) : Prop :=
  let is_two_digits (x : Z) : bool := Z.ltb (Z.abs x) 100 in
  result = fold_right Z.add 0 (filter is_two_digits (firstn (Z.to_nat k) arr)).

Example test_add_elements:
  add_elements_spec [98; 87; 76; 20; -6; 54; 43; 32; 21; 10; 87] 5 275.
Proof.
  unfold add_elements_spec.
  (* Simplify the expression:
     1. Z.to_nat 5 becomes 5%nat.
     2. firstn 5 [...] takes the first 5 elements: [98; 87; 76; 20; -6].
     3. filter checks if abs(x) < 100.
        abs(98)=98 < 100, abs(87)=87 < 100, abs(76)=76 < 100, 
        abs(20)=20 < 100, abs(-6)=6 < 100. All are true.
     4. The list remains [98; 87; 76; 20; -6].
     5. fold_right sums them: 98 + 87 + 76 + 20 + (-6) + 0 = 275.
  *)
  simpl.
  reflexivity.
Qed.