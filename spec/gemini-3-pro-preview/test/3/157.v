Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Definition below_zero_spec (operations : list Z) (result : bool) : Prop :=
  result = true <-> 
  exists n : nat, (0 < n <= length operations)%nat /\ fold_right Z.add 0 (firstn n operations) < 0.

Example test_below_zero_1 : below_zero_spec [99%Z; 100%Z; 28%Z; -50%Z; 20%Z; -10%Z; 28%Z] false.
Proof.
  unfold below_zero_spec.
  split.
  - intros H. inversion H.
  - intros [n [Hbounds Hsum]].
    simpl in Hbounds.
    assert (H_n: n = 1%nat \/ n = 2%nat \/ n = 3%nat \/ n = 4%nat \/ n = 5%nat \/ n = 6%nat \/ n = 7%nat) by lia.
    destruct H_n as [-> | [-> | [-> | [-> | [-> | [-> | -> ]]]]]];
    simpl in Hsum; lia.
Qed.