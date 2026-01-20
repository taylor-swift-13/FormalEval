Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Definition below_zero_spec (operations : list Z) (result : bool) : Prop :=
  result = true <-> 
  exists n : nat, (0 < n <= length operations)%nat /\ fold_right Z.add 0 (firstn n operations) < 0.

Example test_below_zero_case1 : below_zero_spec [1%Z; 0%Z; 0%Z; 0%Z; -1%Z; 3%Z] false.
Proof.
  unfold below_zero_spec.
  split.
  - intros H. inversion H.
  - intros [n [Hbounds Hsum]].
    do 7 (destruct n as [|n]; [ simpl in *; try lia | ]).
    simpl in Hbounds. lia.
Qed.