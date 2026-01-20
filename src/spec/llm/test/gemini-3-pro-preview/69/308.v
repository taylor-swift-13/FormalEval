Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition search (lst : list Z) : Z :=
  let count (x : Z) := fold_right (fun y c => if Z.eq_dec x y then c + 1 else c) 0 lst in
  let valid (x : Z) := x <=? count x in
  let candidates := filter valid lst in
  fold_right Z.max (-1) candidates.

Example test_case_1: search [1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 4%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 2%Z; 1%Z; 2%Z; 2%Z; 2%Z; 18%Z; 3%Z; 3%Z; 4%Z; 4%Z; 5%Z; 5%Z; 6%Z; 6%Z; 7%Z; 7%Z; 7%Z; 7%Z; 8%Z; 8%Z; 8%Z; 9%Z; 7%Z; 9%Z; 10%Z; 10%Z; 10%Z; 4%Z] = 4%Z.
Proof. reflexivity. Qed.