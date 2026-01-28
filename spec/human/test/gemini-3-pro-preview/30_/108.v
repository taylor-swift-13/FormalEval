Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope R_scope.

Inductive is_subsequence {A : Type} : list A -> list A -> Prop :=
  | sub_nil : forall l, is_subsequence [] l
  | sub_cons_match : forall x l1 l2, is_subsequence l1 l2 -> is_subsequence (x :: l1) (x :: l2)
  | sub_cons_skip : forall x l1 l2, is_subsequence l1 l2 -> is_subsequence l1 (x :: l2).

Definition is_positive (r : R) : Prop :=
  r > 0.

Definition problem_30_pre (input : list R) : Prop := True.

Definition problem_30_spec (input : list R) (output : list R) : Prop :=
  is_subsequence output input /\
  (forall r, In r output <-> (In r input /\ is_positive r)).

Example test_get_positive : problem_30_spec [1; 1; 1; 1; 1; 2; 2; 2; 2; 2] [1; 1; 1; 1; 1; 2; 2; 2; 2; 2].
Proof.
  unfold problem_30_spec.
  split.
  - repeat apply sub_cons_match.
    apply sub_nil.
  - intro r.
    unfold is_positive.
    split.
    + intro H_in.
      split.
      * apply H_in.
      * simpl in H_in.
        repeat (destruct H_in as [H_eq | H_in]; [subst; apply IZR_lt; reflexivity | ]).
        contradiction.
    + intros [H_in H_pos].
      apply H_in.
Qed.