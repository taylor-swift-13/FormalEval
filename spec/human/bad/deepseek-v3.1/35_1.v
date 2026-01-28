Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.

Definition problem_35_spec (input : list Z) (output : Z) : Prop :=
  In output input /\
  forall x, In x input -> (x <= output)%Z.

Example test_max_element : problem_35_spec [1%Z; 2%Z; 3%Z] 3%Z.
Proof.
  unfold problem_35_spec.
  split.
  - simpl.
    right.
    right.
    left.
    reflexivity.
  - intros x H.
    simpl in H.
    destruct H as [H|H].
    + subst x.
      unfold Z.le.
      exists 2%Z.
      ring.
    + destruct H as [H|H].
      * subst x.
        unfold Z.le.
        exists 1%Z.
        ring.
      * destruct H as [H|H].
        -- subst x.
           apply Z.le_refl.
        -- contradiction.
Qed.