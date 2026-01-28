Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Definition max_element_spec (l : list Z) (res : Z) : Prop :=
  In res l /\ (forall x, In x l -> x <= res).

Example test_max_element : max_element_spec [1%Z; 3%Z; 3%Z; -25%Z; 6%Z; 7%Z; 6%Z; 8%Z; 9%Z; 9%Z; 13%Z; 9%Z; 9%Z; 10%Z; 10%Z; -120%Z; 10%Z; 12%Z; 12%Z; 13%Z; 13%Z; 13%Z; 13%Z; 13%Z; 13%Z; 14%Z; 14%Z; 15%Z; 15%Z; 15%Z; 17%Z; 17%Z; 18%Z; 19%Z; 20%Z; 15%Z; 3%Z; 19%Z; 1%Z] 20%Z.
Proof.
  unfold max_element_spec.
  split.
  - simpl.
    repeat match goal with
    | [ |- 20 = 20 \/ _ ] => left; reflexivity
    | [ |- 20 = 20 ] => reflexivity
    | [ |- _ \/ _ ] => right
    end.
  - intros x H.
    simpl in H.
    repeat (destruct H as [H|H]; [ subst; try lia | ]).
    contradiction.
Qed.