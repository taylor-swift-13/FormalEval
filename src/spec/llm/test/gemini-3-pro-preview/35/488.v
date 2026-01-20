Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Definition max_element_spec (l : list Z) (res : Z) : Prop :=
  In res l /\ (forall x, In x l -> x <= res).

Example test_max_element : max_element_spec [1000000; 999999; 999998; 999997; 999996; 999995; 999994; 999993; 999992; 999991; 999990; 999989; -150; 999987; 999986; 999985; 999984; 999983; 999982; 999980; 999979; 999978; 999974; 999976; 999975; 999974; 999973; 999972; 999971; 999970] 1000000.
Proof.
  unfold max_element_spec.
  split.
  - simpl.
    left. reflexivity.
  - intros x H.
    simpl in H.
    repeat (destruct H as [H | H]; [subst; lia | ]).
    contradiction.
Qed.