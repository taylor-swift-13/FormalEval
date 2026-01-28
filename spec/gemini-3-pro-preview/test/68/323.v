From Coq Require Import List ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition solution (l : list Z) : list Z :=
  let p x := andb (x mod 2 =? 0) (x <? 10) in
  let c1 := Z.of_nat (length (filter p l)) in
  let c2 := Z.of_nat (length (filter (fun x => negb (p x)) l)) in
  [c1; c2].

Example test_case: solution [7; 9; 1; 5; 3; 11; 13; 15; 17; 19; 21; 22; 31; 25; 27; 29; 31; 33; 34; 39; 4; 2; 7] = [2; 21].
Proof. reflexivity. Qed.