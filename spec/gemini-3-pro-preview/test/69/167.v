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
  fold_right (fun x acc => if Z.leb x (count x l) then Z.max acc x else acc) (-1) l.

Example test_case: search [1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 2; 2; 2; 3; 3; 4; 4; 4; 5; 5; 5; 6; 6; 6; 7; 7; 7; 8; 8; 8; 9; 8; 9; 10; 10; 10; 5; 1] = 2.
Proof. reflexivity. Qed.