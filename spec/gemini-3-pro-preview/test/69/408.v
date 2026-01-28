Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Fixpoint count (val : Z) (l : list Z) : Z :=
  match l with
  | [] => 0
  | h :: t => if val =? h then 1 + count val t else count val t
  end.

Definition search (l : list Z) : Z :=
  let p x := count x l >=? x in
  let candidates := filter p l in
  fold_left Z.max candidates (-1).

Example test_search: search [1; 1; 1; 1; 1; 1; 1; 2; 2; 2; 2; 2; 2; 3; 1; 14; 2; 3; 3; 3; 18; 1; 1; 1] = 3.
Proof. reflexivity. Qed.