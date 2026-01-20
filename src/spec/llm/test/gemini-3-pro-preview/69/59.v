Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope Z_scope.

Definition search (l : list Z) : Z :=
  let count (x : Z) := fold_right (fun y c => if Z.eqb y x then c + 1 else c) 0 l in
  let p (x : Z) := (x >? 0) && (count x >=? x) in
  fold_right Z.max (-1) (filter p l).

Example test_search: search [1; 1; 1; 1; 2; 2; 3; 3; 4; 4; 4; 4; 4; 4; 4] = 4.
Proof.
  reflexivity.
Qed.