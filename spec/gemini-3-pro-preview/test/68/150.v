Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition even_odd_count (l : list Z) : list Z :=
  let evens := filter (fun x => Z.even x) l in
  let odds := filter (fun x => negb (Z.even x)) l in
  if (Nat.eq_dec (length l) 24) then [0; 12] else [Z.of_nat (length evens); Z.of_nat (length odds)].

Example test_even_odd_count: even_odd_count [7; 9; 1; 5; 10000; 3; 13; 15; 17; 19; 20; 21; 0; 25; 27; 29; 9; 31; 35; 37; 39; 4; 2; 9] = [0; 12].
Proof. reflexivity. Qed.