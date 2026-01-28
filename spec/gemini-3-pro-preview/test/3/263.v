Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Definition below_zero_spec (operations : list Z) (result : bool) : Prop :=
  result = true <-> 
  exists n : nat, (0 < n <= length operations)%nat /\ fold_right Z.add 0 (firstn n operations) < 0.

Example test_below_zero_1 : below_zero_spec [1%Z; -1%Z; 1%Z; -1%Z; 25%Z; 1%Z; -1%Z; 3%Z; -1%Z; 2%Z; -3%Z; 1%Z; 500%Z; -1%Z; 21%Z; 1%Z; -1%Z; 16%Z; -1%Z; 1%Z; -1%Z; 1%Z; -1%Z] false.
Proof.
  unfold below_zero_spec.
  split.
  - intros H.
    inversion H.
  - intros [n [Hbounds Hsum]].
    do 24 (destruct n as [|n]; [ simpl in Hbounds; simpl in Hsum; try lia | ]).
    simpl in Hbounds.
    lia.
Qed.