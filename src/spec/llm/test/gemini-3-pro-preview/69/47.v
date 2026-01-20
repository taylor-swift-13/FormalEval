Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition count_occurrences (l : list Z) (z : Z) : Z :=
  fold_right (fun x acc => if Z.eq_dec x z then acc + 1 else acc) 0 l.

Definition search (l : list Z) : Z :=
  let valid x := (count_occurrences l x) >=? x in
  let candidates := filter valid l in
  fold_right Z.max (-1) candidates.

Example test_search: search [1%Z; 1%Z; 1%Z; 1%Z; 2%Z; 2%Z; 2%Z; 3%Z; 3%Z; 4%Z; 7%Z; 4%Z; 4%Z; 4%Z; 4%Z; 4%Z; 4%Z] = 4%Z.
Proof. reflexivity. Qed.