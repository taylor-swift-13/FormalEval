Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Definition below_zero_spec (operations : list Z) (result : bool) : Prop :=
  result = true <-> 
  exists n : nat, (0 < n <= length operations)%nat /\ fold_right Z.add 0 (firstn n operations) < 0.

Example test_below_zero_1 : below_zero_spec [1%Z; 2%Z; 3%Z; 4%Z; 5%Z; -15%Z; 4%Z; 7%Z; 8%Z; 9%Z; -19%Z; 21%Z] false.
Proof.
  unfold below_zero_spec.
  split.
  - intros H. inversion H.
  - intros [n [Hbounds Hsum]].
    do 13 (destruct n as [|n]; [ simpl in Hsum; try lia | ]).
    simpl in Hbounds. lia.
Qed.