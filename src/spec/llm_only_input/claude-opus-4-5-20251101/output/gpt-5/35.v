Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Lia.

Open Scope Z_scope.

Definition max_element_spec (l : list Z) (m : Z) : Prop :=
  l <> nil /\ In m l /\ forall x, In x l -> x <= m.

Example test_max_element : max_element_spec (1%Z :: 2%Z :: 3%Z :: nil) 3%Z.
Proof.
  unfold max_element_spec.
  split.
  - (* l <> nil *)
    discriminate.
  - split.
    + (* In 3 l *)
      simpl. right. right. left. reflexivity.
    + (* forall x, In x l -> x <= 3 *)
      intros x H.
      simpl in H.
      destruct H as [H | [H | [H | H]]].
      * subst x. lia.
      * subst x. lia.
      * subst x. lia.
      * contradiction.
Qed.