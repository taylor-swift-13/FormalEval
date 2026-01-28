Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Definition max_element_spec (l : list Z) (res : Z) : Prop :=
  In res l /\ (forall x, In x l -> x <= res).

Example test_max_element : max_element_spec [999988%Z; 1%Z; 2%Z; 3%Z; 4%Z; 5%Z; 7%Z; 8%Z; -120%Z; 999992%Z; 10%Z; 21%Z; 13%Z; 4%Z; 14%Z; 15%Z; 17%Z; 999976%Z; 19%Z; 20%Z; 999991%Z; 11%Z] 999992%Z.
Proof.
  unfold max_element_spec.
  split.
  - simpl.
    do 9 right. left. reflexivity.
  - intros x H.
    simpl in H.
    do 22 (destruct H as [H|H]; [subst; lia | ]).
    contradiction.
Qed.