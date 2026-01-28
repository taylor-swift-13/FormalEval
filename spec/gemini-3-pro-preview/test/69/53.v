Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition search (lst : list Z) : Z :=
  let count (n : Z) := fold_right (fun x acc => if Z.eq_dec n x then acc + 1 else acc) 0 lst in
  let filtered := filter (fun n => n <=? count n) lst in
  fold_right Z.max (-1) filtered.

Example test_case: search [1; 1; 1; 2; 5; 2; 3; 3] = 2.
Proof.
  compute.
  reflexivity.
Qed.