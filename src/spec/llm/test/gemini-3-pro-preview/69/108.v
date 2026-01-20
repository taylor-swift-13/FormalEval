Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition count_occurrences (lst : list Z) (x : Z) : Z :=
  fold_right (fun y c => if Z.eq_dec y x then c + 1 else c) 0 lst.

Definition search (lst : list Z) : Z :=
  fold_right Z.max (-1) (filter (fun x => count_occurrences lst x >=? x) lst).

Example test_search: search [4%Z; 5%Z; 6%Z; 4%Z; 5%Z; 5%Z; 5%Z] = -1%Z.
Proof.
  compute.
  reflexivity.
Qed.