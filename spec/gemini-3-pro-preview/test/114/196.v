Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition solution (l : list Z) : Z :=
  fold_right (fun n acc => if Z.odd n then n + acc else acc) 0 l.

Example test_case_new: solution [-1%Z; -8%Z; 2%Z; -3%Z; 4%Z; -5%Z; 6%Z; 5%Z; -4%Z; -7%Z; -8%Z; 8%Z; -9%Z; 10%Z] = -20%Z.
Proof. reflexivity. Qed.