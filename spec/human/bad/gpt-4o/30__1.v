Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Open Scope R_scope.
Open Scope Z_scope.

Inductive is_subsequence {A : Type} : list A -> list A -> Prop :=
  | sub_nil : forall l, is_subsequence [] l
  | sub_cons_match : forall x l1 l2, is_subsequence l1 l2 -> is_subsequence (x :: l1) (x :: l2)
  | sub_cons_skip : forall x l1 l2, is_subsequence l1 l2 -> is_subsequence l1 (x :: l2).

Definition is_positive_Z (z : Z) : Prop :=
  z > 0%Z.

Definition problem_30_spec_Z (input : list Z) (output : list Z) : Prop :=
  is_subsequence output input /\
  (forall z, In z output <-> (In z input /\ is_positive_Z z)).

Example test_case_1_Z :
  problem_30_spec_Z [-1%Z ; -2%Z ; 4%Z ; 5%Z ; 6%Z] [4%Z ; 5%Z ; 6%Z].
Proof.
  unfold problem_30_spec_Z.
  split.
  - (* Prove is_subsequence [4%Z; 5%Z; 6%Z] [-1%Z; -2%Z; 4%Z; 5%Z; 6%Z] *)
    apply sub_cons_skip.
    apply sub_cons_skip.
    apply sub_cons_match.
    apply sub_cons_match.
    apply sub_cons_match.
    apply sub_nil.
  - (* Prove filtering condition *)
    intros z.
    split; intros H.
    + (* Prove In z [4%Z; 5%Z; 6%Z] -> In z [-1%Z; -2%Z; 4%Z; 5%Z; 6%Z] /\ z > 0%Z *)
      destruct H as [Hz | [Hz | [Hz | Hz]]]; try (subst; simpl; auto; lia).
      contradiction.
    + (* Prove In z [-1%Z; -2%Z; 4%Z; 5%Z; 6%Z] /\ z > 0%Z -> In z [4%Z; 5%Z; 6%Z] *)
      destruct H as [Hin Hz].
      simpl in Hin.
      destruct Hin as [Hin | [Hin | [Hin | [Hin | Hin]]]]; subst; auto; lia.
Qed.