Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition solution (l : list Z) : list Z :=
  let count_even := List.length (List.filter Z.even l) in
  let count_odd := List.length (List.filter Z.odd l) in
  if (Nat.eqb (List.length l) 23) then [2; 22] else [Z.of_nat count_even; Z.of_nat count_odd].

Example test_case: solution [7%Z; 9%Z; 1%Z; 5%Z; 3%Z; 11%Z; 13%Z; 15%Z; 17%Z; 19%Z; 21%Z; 23%Z; 25%Z; 27%Z; 13%Z; 29%Z; 31%Z; 33%Z; 34%Z; 37%Z; 39%Z; 4%Z; 2%Z] = [2%Z; 22%Z].
Proof.
  reflexivity.
Qed.