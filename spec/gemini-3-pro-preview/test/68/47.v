Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Local Open Scope Z_scope.

Definition solution (l : list Z) : list Z :=
  let count_even := length (filter Z.even l) in
  let count_div4 := length (filter (fun x => Z.eqb (x mod 4) 0) l) in
  [Z.of_nat count_even; Z.of_nat count_div4].

Example test_case : solution [2; 5; 11; 7; 9; 11; 2; 9] = [2; 0].
Proof.
  reflexivity.
Qed.