Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Fixpoint count (v : Z) (l : list Z) : nat :=
  match l with
  | [] => 0%nat
  | x :: xs => if Z.eq_dec v x then S (count v xs) else count v xs
  end.

Definition search (l : list Z) : Z :=
  let f x := (x <=? Z.of_nat (count x l)) in
  let candidates := filter f l in
  fold_right Z.max (-1) candidates.

Example test_search: search [2; 6; 4; 2; 8; 7; 5; 6; 4; 10; 4; 6; 3; 7; 8; 8; 3; 1; 4; 2; 2; 10; 7] = 4.
Proof. reflexivity. Qed.