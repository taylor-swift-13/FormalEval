Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition count_occ (l : list Z) (x : Z) : Z :=
  fold_left (fun acc y => if Z.eq_dec y x then acc + 1 else acc) l 0.

Definition search (l : list Z) : Z :=
  let valid x := x <=? count_occ l x in
  fold_left Z.max (filter valid l) (-1).

Example search_example : search [1%Z; 1%Z; 1%Z; 1%Z; 8%Z; 1%Z; 1%Z; 2%Z; 2%Z; 2%Z; 2%Z; 2%Z; 3%Z; 3%Z; 3%Z; 4%Z; 3%Z; 3%Z; 3%Z; 3%Z] = 3%Z.
Proof. reflexivity. Qed.