Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Lia.
Import ListNotations.

Definition max_element_spec (l : list nat) (m : nat) : Prop :=
  l <> [] /\
  In m l /\
  forall x, In x l -> x <= m.

Example max_element_test : max_element_spec [1; 2; 3] 3.
Proof.
  unfold max_element_spec.
  repeat split.
  - discriminate.
  - simpl. right. right. left. reflexivity.
  - intros x H.
    simpl in H.
    destruct H as [H | [H | [H | H]]].
    + rewrite H. lia.
    + rewrite H. lia.
    + rewrite H. lia.
    + contradiction.
Qed.