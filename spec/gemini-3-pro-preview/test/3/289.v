Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Definition below_zero_spec (operations : list Z) (result : bool) : Prop :=
  result = true <-> 
  exists n : nat, (0 < n <= length operations)%nat /\ fold_right Z.add 0 (firstn n operations) < 0.

Example test_below_zero_large : below_zero_spec [-20; 1; 2; -3; 4; -5; -20; 6; -7; 8; -9; 20; -11; 12; -13; 14; -15; 16; -17; 18; -19; 20; -21; 22; -23; 24; -25; 26; 28; -29; 31; -31; -31; -19] true.
Proof.
  unfold below_zero_spec.
  split.
  - intros _.
    exists 1%nat.
    split.
    + simpl. lia.
    + simpl. lia.
  - intros _. reflexivity.
Qed.