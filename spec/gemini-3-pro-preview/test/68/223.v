Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Fixpoint halve_evens (l : list Z) : list Z :=
  match l with
  | [] => []
  | x :: xs => if Z.even x then (x / 2) :: halve_evens xs else halve_evens xs
  end.

Example test_halve_evens: halve_evens [1; 11; 5; 7; 9; 1] = [].
Proof.
  simpl. reflexivity.
Qed.