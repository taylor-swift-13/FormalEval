Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition count (l : list Z) (x : Z) : Z :=
  fold_right (fun y c => if Z.eqb x y then c + 1 else c) 0 l.

Definition search (l : list Z) : Z :=
  fold_right (fun x acc => if count l x >=? x then Z.max acc x else acc) (-1) l.

Example test_search:
  search [1%Z; 2%Z; 3%Z; 14%Z; 5%Z; 7%Z; 8%Z; 10%Z; 10%Z; 10%Z; 10%Z; 10%Z; 10%Z; 11%Z; 12%Z; 13%Z; 14%Z; 15%Z] = 1%Z.
Proof. reflexivity. Qed.