Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Definition max_element_spec (l : list Z) (max_elem : Z) : Prop :=
  In max_elem l /\ (forall x, In x l -> x <= max_elem).

Example test_max_element : max_element_spec [-5; 2; 9; 4; 5; 6; 7] 9.
Proof.
  unfold max_element_spec.
  split.
  - simpl.
    right. right. left. reflexivity.
  - intros x H.
    simpl in H.
    destruct H as [H | [H | [H | [H | [H | [H | [H | H]]]]]]].
    + rewrite H. lia.
    + rewrite H. lia.
    + rewrite H. lia.
    + rewrite H. lia.
    + rewrite H. lia.
    + rewrite H. lia.
    + rewrite H. lia.
    + contradiction.
Qed.