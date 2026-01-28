Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Definition max_element_spec (l : list Z) (res : Z) : Prop :=
  In res l /\ (forall x, In x l -> x <= res).

Example test_max_element : max_element_spec [8%Z; 6%Z; 6%Z; 4%Z; 3%Z; 99%Z; 3%Z; -4%Z; 8%Z] 99%Z.
Proof.
  unfold max_element_spec.
  split.
  - simpl.
    do 5 right. left. reflexivity.
  - intros x H.
    simpl in H.
    repeat (destruct H as [H | H]; [subst; lia | ]).
    contradiction.
Qed.