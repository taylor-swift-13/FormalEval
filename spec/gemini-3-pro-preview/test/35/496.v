Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Definition max_element_spec (l : list Z) (res : Z) : Prop :=
  In res l /\ (forall x, In x l -> x <= res).

Example test_max_element : max_element_spec [-101; 0; 10; -100; -1000; 10; -100; -100; 10] 10.
Proof.
  unfold max_element_spec.
  split.
  - simpl. tauto.
  - intros x H.
    simpl in H.
    intuition; subst; lia.
Qed.