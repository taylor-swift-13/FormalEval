Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Fixpoint solve (l : list Z) : Z :=
  match l with
  | [] => 0
  | x :: nil => x
  | x :: _ :: xs => x + solve xs
  end.

Example test_case: solve [1%Z; 0%Z; -70%Z; -1%Z; 1%Z; 1%Z; 0%Z; 1%Z; -1%Z; 100000%Z; -1%Z; 2%Z; -1%Z] = (-71)%Z.
Proof. reflexivity. Qed.