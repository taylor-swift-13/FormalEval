Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition solution (l : list Z) : Z := fold_right Z.add 0%Z l.

Example test_case_2: solution [-10%Z; -9%Z; -8%Z; -7%Z; -6%Z; -5%Z; -4%Z; -3%Z; -1%Z; -1%Z] = -54%Z.
Proof.
  simpl.
  reflexivity.
Qed.