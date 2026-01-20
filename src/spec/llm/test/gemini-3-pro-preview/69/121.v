Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Fixpoint count (x : Z) (l : list Z) : Z :=
  match l with
  | [] => 0
  | h :: t => (if x =? h then 1 else 0) + count x t
  end.

Definition search (l : list Z) : Z :=
  let p x := count x l >=? x in
  let l' := filter p l in
  fold_left Z.max l' (-1).

Example test_search: search [1; 1; 2] = 1.
Proof. reflexivity. Qed.