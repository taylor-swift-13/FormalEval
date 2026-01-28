Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Definition below_zero_spec (operations : list Z) (result : bool) : Prop :=
  result = true <-> 
  exists n : nat, (0 < n <= length operations)%nat /\ fold_right Z.add 0 (firstn n operations) < 0.

Example test_below_zero_1 : below_zero_spec [299%Z; -200%Z; 300%Z; -400%Z; 28%Z; 300%Z; -200%Z; 300%Z; 301%Z; 300%Z] true.
Proof.
  unfold below_zero_spec.
  split.
  - intros _.
    exists 4%nat.
    split.
    + simpl. lia.
    + simpl. lia.
  - intros _.
    reflexivity.
Qed.