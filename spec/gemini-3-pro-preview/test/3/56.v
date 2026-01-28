Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Definition below_zero_spec (operations : list Z) (result : bool) : Prop :=
  result = true <-> 
  exists n : nat, (0 < n <= length operations)%nat /\ fold_right Z.add 0 (firstn n operations) < 0.

Example test_below_zero_1 : below_zero_spec [5; 15; -20; 25; -30; 35; -40; 45; -50; -21] true.
Proof.
  unfold below_zero_spec.
  split.
  - intros _.
    exists 5%nat.
    split.
    + simpl. lia.
    + simpl. lia.
  - intros _.
    reflexivity.
Qed.