Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Fixpoint count (v : Z) (l : list Z) : Z :=
  match l with
  | [] => 0
  | x :: xs => (if Z.eq_dec x v then 1 else 0) + count v xs
  end.

Definition search (l : list Z) : Z :=
  let filtered := filter (fun x => count x l >=? x) l in
  fold_left Z.max filtered (-1).

Example test_search: search [1; 2; 3; 4; 5; 6; 18; 7; 8; 9; 8; 10; 10; 10; 10; 10; 11; 12; 13; 14; 15] = 1.
Proof. reflexivity. Qed.