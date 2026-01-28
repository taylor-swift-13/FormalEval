Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition count_occurrences (lst : list Z) (x : Z) : Z :=
  fold_right (fun y acc => if Z.eqb y x then acc + 1 else acc) 0 lst.

Definition search (lst : list Z) : Z :=
  let candidates := filter (fun x => count_occurrences lst x >=? x) lst in
  fold_right Z.max (-1) candidates.

Example test_search: search [5; 5; 4; 3; 5; 5] = -1.
Proof.
  compute.
  reflexivity.
Qed.