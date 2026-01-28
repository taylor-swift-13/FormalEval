Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition count (l : list Z) (x : Z) : Z :=
  fold_right (fun n acc => if Z.eq_dec n x then acc + 1 else acc) 0 l.

Definition search (l : list Z) : Z :=
  fold_right (fun x acc => if count l x >=? x then Z.max x acc else acc) (-1) l.

Example test_search: search [2%Z; 2%Z; 4%Z; 4%Z; 4%Z; 4%Z; 4%Z; 4%Z; 2%Z; 4%Z] = 4%Z.
Proof. reflexivity. Qed.