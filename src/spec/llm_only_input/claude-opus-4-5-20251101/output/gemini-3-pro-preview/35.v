Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Lia.
Import ListNotations.
Open Scope Z_scope.

Definition max_element_spec (l : list Z) (res : Z) : Prop :=
  In res l /\ (forall x, In x l -> x <= res).

Example max_element_test : max_element_spec [1%Z; 2%Z; 3%Z] 3%Z.
Proof.
  unfold max_element_spec.
  split.
  - (* Prove In 3 [1; 2; 3] *)
    simpl. right. right. left. reflexivity.
  - (* Prove forall x, In x [1; 2; 3] -> x <= 3 *)
    intros x H.
    simpl in H.
    destruct H as [H | [H | [H | H]]].
    + subst x. lia.
    + subst x. lia.
    + subst x. lia.
    + contradiction.
Qed.