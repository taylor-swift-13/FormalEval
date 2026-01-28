Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope Z_scope.

Definition count_occurrences (lst : list Z) (x : Z) : Z :=
  fold_left (fun acc y => if Z.eqb y x then (acc + 1) else acc) lst 0.

Definition search (lst : list Z) : Z :=
  let candidates := filter (fun x => x <=? count_occurrences lst x) lst in
  fold_left Z.max candidates (-1).

Example test_search: search [1; 1; 1; 1; 1; 1; 4; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 2; 1; 2; 2; 2; 18; 3; 3; 3; 4; 4; 4; 5; 5; 6; 6; 7; 7; 7; 7; 8; 8; 8; 9; 9; 9; 10; 10; 10] = 4.
Proof.
  vm_compute.
  reflexivity.
Qed.