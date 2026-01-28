Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Definition below_zero_spec (operations : list Z) (result : bool) : Prop :=
  result = true <-> 
  exists n : nat, (0 < n <= length operations)%nat /\ fold_right Z.add 0 (firstn n operations) < 0.

Example test_below_zero_example : below_zero_spec [99; 100; 28; -50; 20; -8; 28] false.
Proof.
  unfold below_zero_spec.
  split.
  - intros H. inversion H.
  - intros [n [Hbounds Hsum]].
    simpl in Hbounds.
    assert (Hn: n = 1%nat \/ n = 2%nat \/ n = 3%nat \/ n = 4%nat \/ n = 5%nat \/ n = 6%nat \/ n = 7%nat) by lia.
    destruct Hn as [Hn | [Hn | [Hn | [Hn | [Hn | [Hn | Hn]]]]]]; subst n; simpl in Hsum; lia.
Qed.