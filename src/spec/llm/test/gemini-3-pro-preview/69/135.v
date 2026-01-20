Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope Z_scope.

Fixpoint count (x : Z) (l : list Z) : Z :=
  match l with
  | [] => 0
  | y :: tl => (if Z.eqb x y then 1 else 0) + count x tl
  end.

Definition search (l : list Z) : Z :=
  let valid (x : Z) := andb (x >? 0) (count x l >=? x) in
  let candidates := filter valid l in
  fold_left Z.max candidates (-1).

Example test_search: search [1; 1; 1; 1; 1; 1; 2; 2; 2; 2; 2; 2; 3; 3; 3; 3; 4; 4; 4; 4; 4; 4; 5; 5; 5; 6; 6; 6; 7; 7; 8; 8; 9; 9; 10; 10; 11; 11; 12; 13] = 4.
Proof.
  vm_compute.
  reflexivity.
Qed.