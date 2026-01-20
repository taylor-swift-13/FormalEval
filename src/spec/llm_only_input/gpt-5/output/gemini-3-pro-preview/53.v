Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Lia.

Import ListNotations.
Open Scope Z_scope.

Definition spec (input : list Z) : Z :=
  fold_right Z.add 0%Z input.

Example test_spec_case:
  spec [0%Z; 1%Z] = 1%Z.
Proof.
  unfold spec.
  cbn.
  lia.
Qed.