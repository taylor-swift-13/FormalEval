Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Fixpoint count (target : Z) (l : list Z) : Z :=
  match l with
  | [] => 0
  | x :: xs => (if Z.eq_dec x target then 1 else 0) + count target xs
  end.

Definition search (l : list Z) : Z :=
  let p x := x <=? count x l in
  let valid := filter p l in
  fold_right Z.max (-1) valid.

Example test_case: search [5; 4; 5; 3; 4; 3; 5; 5; 5; 3] = 5.
Proof. reflexivity. Qed.