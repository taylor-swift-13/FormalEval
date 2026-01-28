Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Fixpoint count (z : Z) (l : list Z) : Z :=
  match l with
  | [] => 0
  | h :: t => if Z.eq_dec h z then 1 + count z t else count z t
  end.

Definition search (l : list Z) : Z :=
  let valid (x : Z) := (count x l >=? x)%Z in
  let candidates := filter valid l in
  fold_right Z.max (-1)%Z candidates.

Example test_search: search [6; 4; 5; 3; 5; 3; 5; 5; 5] = 5.
Proof.
  reflexivity.
Qed.