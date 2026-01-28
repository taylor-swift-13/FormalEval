Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Definition below_zero_spec (operations : list Z) (result : bool) : Prop :=
  result = true <-> 
  exists n : nat, (0 < n <= length operations)%nat /\ fold_right Z.add 0 (firstn n operations) < 0.

Example test_below_zero_custom : below_zero_spec [99; 23; 20; -10] false.
Proof.
  unfold below_zero_spec.
  split.
  - intros H. inversion H.
  - intros [n [Hbounds Hsum]].
    simpl in Hbounds.
    assert (n = 1 \/ n = 2 \/ n = 3 \/ n = 4)%nat as Hcases by lia.
    destruct Hcases as [H | [H | [H | H]]]; subst n; simpl in Hsum; lia.
Qed.