Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition simplify (x n : list Z) : bool :=
  match x, n with
  | [n1; d1], [n2; d2] => (n1 * n2) mod (d1 * d2) =? 0
  | _, _ => false
  end.

Example test_simplify : simplify [-15; 6] [-15; 6] = false.
Proof. reflexivity. Qed.