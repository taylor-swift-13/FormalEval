Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope Z_scope.

Definition solution (l : list Z) : Z :=
  fold_right (fun x acc => if x mod 3 =? 0 then acc + 1 else acc) 0 l.

Example test_example: solution [71; -2; -33; 75; 21; 19] = 3.
Proof.
  reflexivity.
Qed.