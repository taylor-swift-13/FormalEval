Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Fixpoint min_element (l : list Z) : Z :=
  match l with
  | [] => 0
  | [x] => x
  | x :: xs => Z.min x (min_element xs)
  end.

Example test_min_element: min_element [-39; 10; -20; 30; 50; -60; -3; 90; -100] = -100.
Proof.
  simpl. reflexivity.
Qed.