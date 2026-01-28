Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
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

Example test_case : solution [-5; 4; -4; -5; -3; 5; -1; 6] = -13.
Proof.
  reflexivity.
Qed.