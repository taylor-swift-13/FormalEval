Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition solution (l : list Z) : list Z :=
  let count_even := Z.of_nat (length (filter (fun x => Z.even x) l)) in
  let count_special := Z.of_nat (length (filter (fun x => x =? 3) l)) in
  [count_even; count_special].

Example test_case_1 : solution [2; 1; 5; 7; 12; 9; 1] = [2; 0].
Proof.
  reflexivity.
Qed.