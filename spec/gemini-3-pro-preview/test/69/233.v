Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope Z_scope.

Fixpoint count_occurrences (l : list Z) (x : Z) : Z :=
  match l with
  | [] => 0
  | h :: t => (if Z.eqb h x then 1 else 0) + count_occurrences t x
  end.

Definition search (l : list Z) : Z :=
  let valid (x : Z) := (x >? 0) && (count_occurrences l x >=? x) in
  let candidates := filter valid l in
  fold_right Z.max (-1) candidates.

Example test_search: search [1; 1; 1; 1; 1; 1; 1; 2; 2; 2; 2; 2; 2; 3; 1; 14; 2; 3; 3; 3; 18; 1; 1] = 3.
Proof.
  reflexivity.
Qed.