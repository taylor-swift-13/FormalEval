Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition count_occurrences (lst : list Z) (x : Z) : Z :=
  fold_right (fun y c => if Z.eq_dec x y then c + 1 else c) 0 lst.

Definition search (lst : list Z) : Z :=
  let filtered := filter (fun x => x <=? count_occurrences lst x) lst in
  fold_right Z.max (-1) filtered.

Example test_case_1: search [1%Z; 10%Z; 4%Z; 5%Z; 6%Z; 7%Z; 4%Z; 10%Z; 7%Z; 7%Z; 6%Z] = 1%Z.
Proof.
  compute. reflexivity.
Qed.