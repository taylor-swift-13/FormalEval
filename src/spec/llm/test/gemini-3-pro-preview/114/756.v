Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Fixpoint can_arrange_aux (last : Z) (l : list Z) : Z :=
  match l with
  | [] => 0
  | x :: xs => (if x <? last then x else 0) + can_arrange_aux x xs
  end.

Definition can_arrange (l : list Z) : Z :=
  match l with
  | [] => 0
  | x :: xs => can_arrange_aux x xs
  end.

Example test_can_arrange: can_arrange [60; 3; -4; 50000; 5; -6; 7; -8; -3; 2; -1; 60] = -11.
Proof. reflexivity. Qed.