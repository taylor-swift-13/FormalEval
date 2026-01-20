Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition count_occurrences (lst : list Z) (x : Z) : Z :=
  fold_right (fun n c => if Z.eq_dec n x then c + 1 else c) 0 lst.

Definition search (lst : list Z) : Z :=
  let candidates := filter (fun x => count_occurrences lst x >=? x) lst in
  fold_right Z.max (-1) candidates.

Example test_search: search [7%Z; 9%Z; 9%Z; 9%Z; 3%Z; 4%Z; 1%Z; 5%Z; 9%Z; 1%Z; 2%Z; 1%Z; 1%Z; 10%Z; 7%Z; 5%Z; 6%Z; 7%Z; 6%Z; 7%Z; 7%Z; 6%Z] = 1%Z.
Proof. reflexivity. Qed.