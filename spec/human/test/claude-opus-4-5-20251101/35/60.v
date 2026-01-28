Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Lia.
Import ListNotations.
Open Scope Z_scope.

Definition problem_35_pre (input : list Z) : Prop := input <> []%list.

Definition problem_35_spec (input : list Z) (output : Z) : Prop :=
  In output input /\
  forall x, In x input -> (x <= output)%Z.

Example test_problem_35 : problem_35_spec [(-5); 99; 2; 48; 9; 4; 6; 7; 2] 99.
Proof.
  unfold problem_35_spec.
  split.
  - simpl. right. left. reflexivity.
  - intros x Hx.
    simpl in Hx.
    destruct Hx as [H1 | [H2 | [H3 | [H4 | [H5 | [H6 | [H7 | [H8 | [H9 | H10]]]]]]]]].
    + subst x. lia.
    + subst x. lia.
    + subst x. lia.
    + subst x. lia.
    + subst x. lia.
    + subst x. lia.
    + subst x. lia.
    + subst x. lia.
    + subst x. lia.
    + contradiction.
Qed.