Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition search (l : list Z) : Z :=
  let count (x : Z) := fold_right (fun y c => if Z.eq_dec x y then c + 1 else c) 0 l in
  fold_right (fun x acc => if x <=? count x then Z.max acc x else acc) (-1) l.

Example test_case: search [1%Z; 5%Z; 1%Z; 2%Z; 2%Z; 2%Z; 3%Z; 3%Z; 2%Z] = 2%Z.
Proof. reflexivity. Qed.