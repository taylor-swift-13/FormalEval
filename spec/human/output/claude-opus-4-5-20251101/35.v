Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Lia.
Import ListNotations.

(* Pre: input must be non-empty *)
Definition problem_35_pre (input : list Z) : Prop := input <> []%list.

Definition problem_35_spec (input : list Z) (output : Z) : Prop :=
  In output input /\
  forall x, In x input -> (x <= output)%Z.

Example test_problem_35 : problem_35_spec [1%Z; 2%Z; 3%Z] 3%Z.
Proof.
  unfold problem_35_spec.
  split.
  - (* Prove In 3 [1; 2; 3] *)
    simpl. right. right. left. reflexivity.
  - (* Prove forall x, In x [1; 2; 3] -> x <= 3 *)
    intros x Hx.
    simpl in Hx.
    destruct Hx as [H1 | [H2 | [H3 | H4]]].
    + subst x. lia.
    + subst x. lia.
    + subst x. lia.
    + contradiction.
Qed.