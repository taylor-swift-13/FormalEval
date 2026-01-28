Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Definition below_zero_spec (operations : list Z) (result : bool) : Prop :=
  result = true <-> 
  exists n : nat, (0 < n <= length operations)%nat /\ fold_right Z.add 0 (firstn n operations) < 0.

Example test_below_zero_1 : below_zero_spec [99%Z; 100%Z; 101%Z; 28%Z; -50%Z; 20%Z; -10%Z; 99%Z] false.
Proof.
  unfold below_zero_spec.
  split.
  - intros H. inversion H.
  - intros [n [Hbounds Hsum]].
    simpl in Hbounds.
    assert (Hn : (n = 1 \/ n = 2 \/ n = 3 \/ n = 4 \/ n = 5 \/ n = 6 \/ n = 7 \/ n = 8)%nat) by lia.
    destruct Hn as [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]];
      simpl in Hsum; lia.
Qed.