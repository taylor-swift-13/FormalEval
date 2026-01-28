Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Definition below_zero_spec (operations : list Z) (result : bool) : Prop :=
  result = true <-> 
  exists n : nat, (0 < n <= length operations)%nat /\ fold_right Z.add 0 (firstn n operations) < 0.

Example test_below_zero_zeros : below_zero_spec [0; 0; 0; 0] false.
Proof.
  unfold below_zero_spec.
  split.
  - intros H.
    inversion H.
  - intros [n [Hbounds Hsum]].
    destruct n; [lia|].
    destruct n; [simpl in Hsum; lia|].
    destruct n; [simpl in Hsum; lia|].
    destruct n; [simpl in Hsum; lia|].
    destruct n; [simpl in Hsum; lia|].
    simpl in Hbounds.
    lia.
Qed.