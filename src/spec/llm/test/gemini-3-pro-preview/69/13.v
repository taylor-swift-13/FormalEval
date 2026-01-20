Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Fixpoint min_element (l : list Z) : Z :=
  match l with
  | [] => 0
  | [x] => x
  | x :: xs => Z.min x (min_element xs)
  end.

Example test_min_element : min_element [1%Z] = 1%Z.
Proof. reflexivity. Qed.