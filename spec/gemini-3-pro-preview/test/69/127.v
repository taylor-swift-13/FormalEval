Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition count (n : Z) (l : list Z) : Z :=
  fold_right (fun x acc => if Z.eqb x n then acc + 1 else acc) 0 l.

Definition search (l : list Z) : Z :=
  fold_right (fun x acc => if count x l >=? x then Z.max acc x else acc) (-1) l.

Example test_case: search [1; 1; 1; 1; 1; 1; 1; 1; 2; 2; 2; 2; 2; 2; 2; 3; 3; 3; 4; 4] = 3.
Proof.
  compute. reflexivity.
Qed.