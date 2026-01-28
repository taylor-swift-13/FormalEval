Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Lia.
Import ListNotations.

(* Pre: input must be non-empty *)
Definition problem_35_pre (input : list Z) : Prop := input <> []%list.

Definition problem_35_spec (input : list Z) (output : Z) : Prop :=
  In output input /\
  forall x, In x input -> (x <= output)%Z.

Example test_problem_35 : problem_35_spec [8%Z; 6%Z; 6%Z; 4%Z; 3%Z; 98%Z; 3%Z; 8%Z] 98%Z.
Proof.
  unfold problem_35_spec.
  split.
  - simpl. right. right. right. right. right. left. reflexivity.
  - intros x Hx.
    simpl in Hx.
    destruct Hx as [H1 | [H2 | [H3 | [H4 | [H5 | [H6 | [H7 | [H8 | H9]]]]]]]].
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