Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Definition below_zero_spec (operations : list Z) (result : bool) : Prop :=
  result = true <-> 
  exists n : nat, (0 < n <= length operations)%nat /\ fold_right Z.add 0 (firstn n operations) < 0.

Example test_below_zero_case1 : below_zero_spec [1%Z; -1%Z; 1%Z; -1%Z; 20%Z; 1%Z; -1%Z; 26%Z; -1%Z; 1%Z; 7%Z; -3%Z; 1%Z; -1%Z; 1%Z; -1%Z; -2%Z; -1%Z; 1%Z; -1%Z; 1%Z; -29%Z; -2%Z; 1%Z; -1%Z; 26%Z] false.
Proof.
  unfold below_zero_spec.
  split.
  - intros H. inversion H.
  - intros [n [Hbounds Hsum]].
    do 30 (destruct n; [ simpl in Hsum; try lia | ]).
    simpl in Hbounds. lia.
Qed.