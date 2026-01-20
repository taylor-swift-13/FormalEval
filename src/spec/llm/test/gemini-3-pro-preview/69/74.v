Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope Z_scope.

Definition count_occurrences (lst : list Z) (x : Z) : Z :=
  fold_right (fun y acc => if Z.eqb x y then acc + 1 else acc) 0 lst.

Definition search (lst : list Z) : Z :=
  let valid (x : Z) := Z.leb x (count_occurrences lst x) in
  let candidates := filter valid lst in
  fold_right Z.max (-1) candidates.

Example test_search_2: search [2; 4; 4; 4; 4] = 4.
Proof.
  compute.
  reflexivity.
Qed.