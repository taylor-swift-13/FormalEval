Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Definition below_zero_spec (operations : list Z) (result : bool) : Prop :=
  result = true <-> 
  exists n : nat, (0 < n <= length operations)%nat /\ fold_right Z.add 0 (firstn n operations) < 0.

Example test_empty_list : below_zero_spec [] false.
Proof.
  unfold below_zero_spec.
  split.
  - intros H. discriminate H.
  - intros [n [Hbound Hsum]].
    simpl in Hbound.
    lia.
Qed.