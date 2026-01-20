Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.

Import ListNotations.
Open Scope Z_scope.

Definition max_element_spec (l : list Z) (m : Z) : Prop :=
  l <> nil /\ In m l /\ forall x, In x l -> x <= m.

Example max_element_spec_test :
  max_element_spec [1000000%Z; 999999%Z; 999998%Z; 999997%Z; 999996%Z; 999995%Z; 999994%Z; 999993%Z; 999992%Z; 999991%Z; 999990%Z; 999989%Z; 999988%Z; -95%Z; 999987%Z; 999986%Z; 999985%Z; 999984%Z; 999983%Z; 999982%Z; 999981%Z; 999980%Z; 999979%Z; 999978%Z; 999977%Z; 999976%Z; 999975%Z; 999974%Z; 999973%Z; 999972%Z; 999971%Z; 999970%Z; 999978%Z; 999998%Z] 1000000%Z.
Proof.
  unfold max_element_spec.
  repeat split.
  - discriminate.
  - simpl. left. reflexivity.
  - intros x H.
    simpl in H.
    repeat (destruct H as [H|H]; [subst; try lia|]).
    contradiction.
Qed.