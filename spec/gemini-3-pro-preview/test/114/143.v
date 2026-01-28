Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Arith.Arith.
Import ListNotations.
Open Scope Z_scope.

Fixpoint solution_aux (l : list Z) (i : nat) : Z :=
  match l with
  | [] => 0
  | x :: xs => (if (i mod 6 =? 3)%nat then x else 0) + solution_aux xs (S i)
  end.

Definition solution (l : list Z) : Z := solution_aux l 0.

Example test_case_1: solution [1%Z; -2%Z; 3%Z; -4%Z; 5%Z; -6%Z; 7%Z; -8%Z; 9%Z; -10%Z; -4%Z] = -14%Z.
Proof. reflexivity. Qed.