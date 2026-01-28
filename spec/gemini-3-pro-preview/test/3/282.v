Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Definition below_zero_spec (operations : list Z) (result : bool) : Prop :=
  result = true <-> 
  exists n : nat, (0 < n <= length operations)%nat /\ fold_right Z.add 0 (firstn n operations) < 0.

Example test_below_zero_new : below_zero_spec [26%Z; 1%Z; 2%Z; -4%Z; 4%Z; 25%Z; 2%Z; -2%Z; -2%Z; -1%Z; -1%Z; -1%Z; -1%Z; -1%Z; -1%Z; 1%Z; 25%Z; 2%Z] false.
Proof.
  unfold below_zero_spec.
  split.
  - intros H. inversion H.
  - intros [n [Hbounds Hsum]].
    do 19 (destruct n; [ simpl in Hsum; simpl in Hbounds; try lia | ]).
    simpl in Hbounds. lia.
Qed.