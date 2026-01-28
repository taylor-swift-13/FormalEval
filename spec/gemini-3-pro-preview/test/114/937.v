Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition solution (l : list Z) : Z :=
  fold_right Z.add 0 (filter (fun x => Z.eqb (Z.abs x) 1) l).

Example test_case: solution [-1; 1; -1; 1; -1; 1; -1; 1; -1; 1; -1; 0; -1; 0; -1] = -3.
Proof. reflexivity. Qed.