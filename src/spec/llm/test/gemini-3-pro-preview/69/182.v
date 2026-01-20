Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition count (n : Z) (l : list Z) : Z :=
  fold_right (fun x acc => if Z.eq_dec x n then acc + 1 else acc) 0 l.

Definition search (l : list Z) : Z :=
  fold_right (fun x acc => if x <=? count x l then Z.max acc x else acc) (-1) l.

Example test_case_1: search [1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 2%Z; 2%Z; 2%Z; 3%Z; 3%Z; 3%Z; 4%Z; 4%Z; 4%Z; 5%Z; 5%Z; 5%Z; 6%Z; 6%Z; 6%Z; 7%Z; 7%Z; 7%Z; 8%Z; 8%Z; 8%Z; 9%Z; 9%Z; 9%Z; 10%Z; 10%Z; 10%Z; 5%Z] = 3%Z.
Proof. reflexivity. Qed.