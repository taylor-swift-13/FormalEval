Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition count_occurrences (lst : list Z) (x : Z) : Z :=
  fold_right (fun y acc => if Z.eq_dec y x then acc + 1 else acc) 0 lst.

Definition search (lst : list Z) : Z :=
  let valid (x : Z) := Z.leb x (count_occurrences lst x) in
  let filtered := filter valid lst in
  fold_right Z.max (-1) filtered.

Example test_search: search [1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 2%Z; 2%Z; 2%Z; 2%Z; 2%Z; 3%Z; 3%Z; 3%Z; 3%Z; 3%Z; 4%Z; 4%Z; 4%Z; 4%Z; 4%Z] = 4%Z.
Proof.
  compute.
  reflexivity.
Qed.