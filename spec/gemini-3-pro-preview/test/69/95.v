Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition count_occurrences (lst : list Z) (x : Z) : Z :=
  fold_right (fun y acc => if Z.eq_dec x y then acc + 1 else acc) 0 lst.

Definition search (lst : list Z) : Z :=
  let valid x := (count_occurrences lst x) >=? x in
  let candidates := filter valid lst in
  fold_right Z.max (-1) candidates.

Example test_case_1 : search [6%Z; 4%Z; 5%Z; 6%Z; 3%Z; 5%Z; 3%Z; 5%Z; 5%Z; 5%Z; 4%Z] = 5%Z.
Proof. reflexivity. Qed.