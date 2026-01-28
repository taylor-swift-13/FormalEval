Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition count_occ (lst : list Z) (x : Z) : Z :=
  fold_right (fun n acc => if Z.eq_dec n x then acc + 1 else acc) 0 lst.

Definition search (lst : list Z) : Z :=
  let valid := filter (fun x => count_occ lst x >=? x) lst in
  fold_right Z.max (-1) valid.

Example test_case : search [1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 4%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 2%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 2%Z; 1%Z; 5%Z; 2%Z; 2%Z; 18%Z; 3%Z; 3%Z; 4%Z; 4%Z; 4%Z; 5%Z; 12%Z; 5%Z; 4%Z; 6%Z; 6%Z; 7%Z; 7%Z; 7%Z; 7%Z; 8%Z; 8%Z; 8%Z; 9%Z; 14%Z; 9%Z; 10%Z; 10%Z; 10%Z] = 4%Z.
Proof. reflexivity. Qed.