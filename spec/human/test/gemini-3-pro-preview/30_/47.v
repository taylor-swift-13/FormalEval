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

Example test_get_positive : problem_30_spec [0] [].
Proof.
  unfold problem_30_spec.
  split.
  - (* Part 1: subsequence *)
    apply sub_nil.
  - (* Part 2: equivalence *)
    intro r.
    unfold is_positive.
    split.
    + (* In output -> In input /\ r > 0 *)
      intro H_in_out.
      inversion H_in_out.
    + (* In input /\ r > 0 -> In output *)
      intros [H_in_in H_pos].
      simpl in H_in_in.
      destruct H_in_in as [H0 | H_nil].
      * subst r.
        exfalso.
        apply (Rlt_irrefl 0 H_pos).
      * contradiction.
Qed.