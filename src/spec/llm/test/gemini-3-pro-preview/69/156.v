Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope Z_scope.

Fixpoint count (x : Z) (l : list Z) : Z :=
  match l with
  | [] => 0
  | h :: t => (if h =? x then 1 else 0) + count x t
  end.

Definition search (l : list Z) : Z :=
  let valid (x : Z) := andb (x >? 0) (count x l >=? x) in
  let candidates := filter valid l in
  fold_right Z.max (-1) candidates.

Example test_search:
  search [1; 1; 1; 1; 1; 1; 2; 2; 2; 2; 2; 3; 3; 3; 3; 3; 3; 3; 3] = 3.
Proof.
  vm_compute.
  reflexivity.
Qed.