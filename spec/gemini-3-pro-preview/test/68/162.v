Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition is_even_digit (n : Z) : bool :=
  (0 <=? n) && (n <=? 9) && (Z.even n).

Definition solve (l : list Z) : list Z :=
  let evens := length (filter is_even_digit l) in
  let odds := length (filter (fun x => negb (is_even_digit x)) l) in
  [Z.of_nat evens; Z.of_nat odds].

Example test_case_2 : solve [7; 9; 1; 5; 10000; 3; 13; 15; 17; 19; 21; 23; 25; 27; 29; 9; 31; 35; 37; 39; 4; 2; 9] = [2; 21].
Proof. reflexivity. Qed.