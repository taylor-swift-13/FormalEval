Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition count_occ (l : list Z) (x : Z) : Z :=
  Z.of_nat (length (filter (fun y => Z.eqb x y) l)).

Definition search (l : list Z) : Z :=
  let valid (x : Z) := (count_occ l x >=? x) in
  let candidates := filter valid l in
  fold_left Z.max candidates (-1).

Example search_example : search [1; 1; 1; 1; 1; 1; 2; 2; 2; 2; 2; 3; 3; 3; 3; 4; 4; 12; 4; 4; 4; 4; 5; 5; 5; 6; 10; 6; 12; 7; 8; 8; 9; 9; 10; 10; 11; 11; 12; 13; 5; 11] = 4.
Proof. reflexivity. Qed.