Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition count_occ (lst : list Z) (x : Z) : Z :=
  fold_right (fun y acc => if Z.eq_dec y x then acc + 1 else acc) 0 lst.

Definition search (lst : list Z) : Z :=
  let filtered := filter (fun x => count_occ lst x >=? x) lst in
  fold_right Z.max (-1) filtered.

Example test_search: search [1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 2%Z; 2%Z; 2%Z; 2%Z; 2%Z; 3%Z; 3%Z; 3%Z; 3%Z; 4%Z; 4%Z; 4%Z; 4%Z; 4%Z; 4%Z; 5%Z; 5%Z; 5%Z; 6%Z; 6%Z; 6%Z; 7%Z; 7%Z; 8%Z; 8%Z; 9%Z; 9%Z; 10%Z; 10%Z; 11%Z; 11%Z; 12%Z; 13%Z; 7%Z] = 4%Z.
Proof. reflexivity. Qed.