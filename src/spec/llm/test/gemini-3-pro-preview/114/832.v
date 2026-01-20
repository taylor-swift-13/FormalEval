Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Fixpoint solution (l : list Z) : Z :=
  match l with
  | [] => 0
  | x :: xs => x + match xs with
                   | [] => 0
                   | _ :: ys => solution ys
                   end
  end.

Example test_solution: solution [-1%Z; 1%Z; -1%Z; 0%Z; 1%Z; -1%Z; 1%Z; -1%Z; 1%Z; -1%Z; -2%Z; 1%Z; -1%Z; 0%Z; -1%Z; 1%Z; -1%Z] = -4%Z.
Proof. reflexivity. Qed.