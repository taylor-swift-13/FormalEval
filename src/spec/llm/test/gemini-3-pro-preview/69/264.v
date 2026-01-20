Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope Z_scope.

Definition count (n : Z) (l : list Z) : Z :=
  fold_right (fun x acc => if Z.eqb x n then acc + 1 else acc) 0 l.

Definition search (l : list Z) : Z :=
  fold_right (fun x max_val => 
    if (max_val <? x) && (x <=? count x l) then x else max_val
  ) (-1) l.

Example test_search: search [1; 1; 1; 1; 1; 1; 2; 2; 2; 2; 2; 3; 3; 3; 3; 4; 4; 4; 4; 4; 4; 5; 5; 5; 6; 6; 6; 7; 7; 13; 8; 9; 9; 10; 10; 11; 11; 12; 13; 4; 7; 1] = 4.
Proof.
  reflexivity.
Qed.