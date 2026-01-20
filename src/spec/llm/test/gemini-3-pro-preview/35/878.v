Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Definition max_element_spec (l : list Z) (res : Z) : Prop :=
  In res l /\ (forall x, In x l -> x <= res).

Example test_max_element : max_element_spec [1%Z; 2%Z; 3%Z; 4%Z; 5%Z; 7%Z; 12%Z; 8%Z; 999992%Z; 10%Z; 11%Z; 12%Z; 12%Z; 13%Z; 14%Z; 15%Z; 16%Z; 17%Z; 999976%Z; 19%Z; 20%Z; 15%Z; 11%Z] 999992%Z.
Proof.
  unfold max_element_spec.
  split.
  - simpl. tauto.
  - intros x H.
    simpl in H.
    repeat destruct H as [H | H]; try (subst; lia); try contradiction.
Qed.