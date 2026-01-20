Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.

Import ListNotations.
Open Scope Z_scope.

Definition max_element_spec (l : list Z) (m : Z) : Prop :=
  l <> nil /\ In m l /\ forall x, In x l -> x <= m.

Example max_element_spec_test :
  max_element_spec [3%Z; 2%Z; 2%Z; 2%Z; 2%Z; 2%Z; 3%Z; 2%Z] 3%Z.
Proof.
  unfold max_element_spec.
  repeat split.
  - discriminate.
  - simpl. left. reflexivity.
  - intros x H.
    simpl in H.
    destruct H as [H0|[H1|[H2|[H3|[H4|[H5|[H6|[H7|[]]]]]]]]]; subst; lia.
Qed.