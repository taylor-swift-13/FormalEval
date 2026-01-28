Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition count_occurrences (l : list Z) (n : Z) : Z :=
  fold_right (fun x acc => if Z.eq_dec x n then acc + 1 else acc) 0 l.

Definition search (l : list Z) : Z :=
  let filtered := filter (fun x => x <=? count_occurrences l x) l in
  fold_right Z.max (-1) filtered.

Example search_test : search [1%Z; 2%Z; 3%Z; 4%Z; 5%Z; 4%Z; 18%Z; 7%Z; 8%Z; 9%Z; 8%Z; 10%Z; 10%Z; 10%Z; 10%Z; 10%Z; 10%Z; 11%Z; 12%Z; 13%Z; 14%Z; 15%Z; 10%Z] = 1%Z.
Proof. reflexivity. Qed.