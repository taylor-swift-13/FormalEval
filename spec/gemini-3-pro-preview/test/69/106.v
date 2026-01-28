Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Fixpoint count (v : Z) (l : list Z) : Z :=
  match l with
  | [] => 0
  | x :: xs => if Z.eq_dec x v then 1 + count v xs else count v xs
  end.

Definition search (l : list Z) : Z :=
  let p x := x <=? count x l in
  let valid := filter p l in
  fold_left Z.max valid (-1).

Example test_case: search [1; 1; 1; 2; 2; 2; 3; 3; 4; 7; 4; 4; 4; 4; 4; 4; 3; 3] = 4.
Proof.
  reflexivity.
Qed.