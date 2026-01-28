Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition count_occurrences (lst : list Z) (x : Z) : Z :=
  fold_right (fun y acc => if Z.eqb x y then acc + 1 else acc) 0 lst.

Definition search (lst : list Z) : Z :=
  fold_right (fun x acc => 
    if x <=? count_occurrences lst x then Z.max acc x else acc
  ) (-1) lst.

Example search_example:
  search [1%Z; 1%Z; 1%Z; 2%Z; 2%Z; 2%Z; 3%Z; 3%Z; 4%Z; 7%Z; 4%Z; 4%Z; 4%Z; 4%Z; 4%Z; 4%Z] = 4%Z.
Proof.
  reflexivity.
Qed.