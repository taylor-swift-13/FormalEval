Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Fixpoint count (x : Z) (l : list Z) : Z :=
  match l with
  | [] => 0
  | y :: tl => (if Z.eq_dec x y then 1 else 0) + count x tl
  end.

Definition search (l : list Z) : Z :=
  let p x := x <=? count x l in
  let candidates := filter p l in
  fold_right Z.max (-1) candidates.

Example test_case: search [3%Z; 3%Z] = -1%Z.
Proof. reflexivity. Qed.