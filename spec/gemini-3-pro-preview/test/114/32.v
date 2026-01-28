Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Fixpoint count (z : Z) (l : list Z) : nat :=
  match l with
  | [] => 0%nat
  | x :: xs => if Z.eqb z x then S (count z xs) else count z xs
  end.

Definition solution (l : list Z) : Z :=
  let unique := filter (fun z => Nat.eqb (count z l) 1) l in
  match unique with
  | [] => 0
  | x :: xs => fold_left Z.min xs x
  end.

Example test_case: solution [3%Z; 2%Z; -5%Z; 4%Z; 2%Z; -3%Z; 2%Z; 5%Z] = (-5)%Z.
Proof.
  compute. reflexivity.
Qed.