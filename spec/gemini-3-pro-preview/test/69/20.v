Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope Z_scope.

Fixpoint count (x : Z) (l : list Z) : Z :=
  match l with
  | [] => 0
  | h :: t => (if Z.eqb x h then 1 else 0) + count x t
  end.

Definition search (l : list Z) : Z :=
  let valid x := (0 <? x) && (x <=? count x l) in
  let candidates := filter valid l in
  fold_right Z.max (-1) candidates.

Example test_case: search [5; 5; 3; 9; 5; 6; 3; 2; 8; 5; 6; 10; 10; 6; 8; 4; 10; 7; 7; 10; 8] = -1.
Proof. reflexivity. Qed.