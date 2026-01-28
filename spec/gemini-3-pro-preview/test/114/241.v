Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition unique (l : list Z) : list Z :=
  nodup Z.eq_dec l.

Definition solution (l : list Z) : Z :=
  fold_right Z.add 0 (unique (filter Z.even l)).

Example test_case: solution [1; 1; -2; 1; -1; 1; -1; 1; -1; 1; -1; -40; 1; -1; 1] = -42.
Proof.
  reflexivity.
Qed.