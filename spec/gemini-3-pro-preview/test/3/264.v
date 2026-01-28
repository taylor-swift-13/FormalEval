Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Definition below_zero_spec (operations : list Z) (result : bool) : Prop :=
  result = true <-> 
  exists n : nat, (0 < n <= length operations)%nat /\ fold_right Z.add 0 (firstn n operations) < 0.

Example test_below_zero_1 : below_zero_spec [99; 100; 28; -50; 20; -9; 28] false.
Proof.
  unfold below_zero_spec.
  split.
  - intros H.
    inversion H.
  - intros [n [Hbounds Hsum]].
    simpl in Hbounds.
    assert (n = 1 \/ n = 2 \/ n = 3 \/ n = 4 \/ n = 5 \/ n = 6 \/ n = 7)%nat as Hn by lia.
    destruct Hn as [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]; simpl in Hsum; lia.
Qed.