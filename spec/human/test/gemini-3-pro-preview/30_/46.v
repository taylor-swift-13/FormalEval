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

Example test_get_positive : problem_30_spec [-2; -1; -1; -3; -4; -1; -3; -1] [].
Proof.
  unfold problem_30_spec.
  split.
  - apply sub_nil.
  - intro r.
    unfold is_positive.
    split.
    + intro H. inversion H.
    + intros [H_in H_pos].
      simpl in H_in.
      destruct H_in as [H | [H | [H | [H | [H | [H | [H | [H | H]]]]]]]];
      try contradiction;
      subst r;
      match type of H_pos with
      | ?X > 0 =>
        assert (Hn: X < 0) by (apply IZR_lt; reflexivity);
        apply (Rlt_asym _ _ Hn H_pos)
      end.
Qed.