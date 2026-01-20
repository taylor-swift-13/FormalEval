Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope Z_scope.

Definition search (lst : list Z) : Z :=
  let count (n : Z) := fold_right (fun x acc => if Z.eq_dec x n then acc + 1 else acc) 0 lst in
  let valid (x : Z) := (x >? 0) && (count x >=? x) in
  let candidates := filter valid lst in
  fold_right Z.max (-1) candidates.

Example test_case: search [1; 8; 1; 2; 2; 2; 2; 3; 3; 2] = 2.
Proof.
  reflexivity.
Qed.