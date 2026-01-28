Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Fixpoint solution (l : list Z) : Z :=
  match l with
  | [] => 0
  | _ :: [] => 0
  | _ :: y :: ys => y + solution ys
  end.

Example test_case_1: solution [-1; -8; 2; -3; 4; -5; 6; -7; 8; -1; -9; 10; 8] = -14.
Proof. simpl. reflexivity. Qed.