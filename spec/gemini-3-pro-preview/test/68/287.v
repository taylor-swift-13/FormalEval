Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope Z_scope.

Definition solve (l : list Z) : list Z :=
  let evens := filter (fun x => Z.even x && negb (x mod 10 =? 0)) l in
  let odds := filter (fun x => Z.odd x && negb (x mod 10 =? 0)) l in
  [Z.of_nat (length evens); Z.of_nat (length odds)].

Example test_case_new: solve [7; 9; 1; 5; 10000; 3; 11; 13; 15; 17; 19; 21; 23; 25; 27; 29; 9; 31; 33; 37; 39; 4; 2; 9; 3] = [2; 22].
Proof.
  vm_compute. reflexivity.
Qed.