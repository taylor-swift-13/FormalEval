Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Fixpoint count (x : Z) (l : list Z) : Z :=
  match l with
  | [] => 0
  | y :: tl => if Z.eq_dec y x then 1 + count x tl else count x tl
  end.

Definition search (l : list Z) : Z :=
  let candidates := filter (fun x => x <=? count x l) l in
  fold_left Z.max candidates (-1).

Example test_search: search [1; 1; 1; 1; 1; 2; 2; 2; 2; 2; 3; 3; 3; 3; 4; 4; 4; 4; 4; 4; 5; 5; 5; 6; 6; 6; 7; 7; 8; 8; 9; 9; 10; 10; 11; 11; 12; 13] = 4.
Proof. reflexivity. Qed.