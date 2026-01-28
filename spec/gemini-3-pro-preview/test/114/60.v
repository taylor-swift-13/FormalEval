Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Fixpoint solution (l : list Z) : Z :=
  match l with
  | [] => 0
  | x :: xs => x + match xs with
                   | [] => 0
                   | _ :: ys => solution ys
                   end
  end.

Example test_case: solution [-2; 1; -4; 6; -7; 0; -4; -5; 1] = -16.
Proof. reflexivity. Qed.