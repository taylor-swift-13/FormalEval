Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition count_occurrences (lst : list Z) (x : Z) : Z :=
  fold_right (fun y acc => if Z.eqb x y then acc + 1 else acc) 0 lst.

Definition search (lst : list Z) : Z :=
  let p x := Z.geb (count_occurrences lst x) x in
  let valid := filter p lst in
  fold_right Z.max (-1) valid.

Example test_search: search [1%Z; 1%Z; 1%Z; 8%Z; 2%Z; 2%Z; 3%Z; 3%Z; 4%Z; 7%Z; 4%Z; 4%Z; 4%Z; 4%Z; 4%Z; 4%Z; 3%Z; 4%Z; 2%Z] = 4%Z.
Proof. reflexivity. Qed.