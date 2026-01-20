Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition count (x : Z) (l : list Z) : Z :=
  fold_right (fun y c => if Z.eq_dec x y then 1 + c else c) 0 l.

Definition search (l : list Z) : Z :=
  fold_right (fun x acc => if x <=? count x l then Z.max acc x else acc) (-1) l.

Example test_search: search [1%Z; 1%Z; 1%Z; 1%Z; 3%Z; 1%Z; 2%Z; 2%Z; 2%Z; 2%Z; 2%Z; 3%Z; 3%Z; 3%Z; 3%Z; 4%Z; 4%Z; 4%Z; 4%Z; 4%Z; 4%Z; 5%Z; 5%Z; 5%Z; 6%Z; 6%Z; 6%Z; 7%Z; 7%Z; 8%Z; 7%Z; 9%Z; 9%Z; 10%Z; 10%Z; 11%Z; 11%Z; 12%Z; 13%Z; 4%Z; 7%Z; 7%Z] = 4%Z.
Proof.
  compute. reflexivity.
Qed.