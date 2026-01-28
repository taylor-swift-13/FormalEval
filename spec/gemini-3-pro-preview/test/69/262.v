Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope Z_scope.

Definition count (n : Z) (l : list Z) : Z :=
  fold_right (fun x acc => if Z.eqb x n then acc + 1 else acc) 0 l.

Definition search (l : list Z) : Z :=
  fold_right (fun x acc => if (x >? acc) && (count x l >=? x) then x else acc) (-1) l.

Example test_search: search [1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 9; 1; 1; 1; 1; 1; 1; 1; 1; 2; 2; 2; 3; 3; 3; 4; 4; 4; 5; 5; 5; 6; 6; 6; 7; 7; 7; 8; 8; 8; 9; 9; 9; 10; 10; 1] = 3.
Proof.
  vm_compute.
  reflexivity.
Qed.