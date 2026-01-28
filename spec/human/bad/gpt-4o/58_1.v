Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Sorting.Sorted.
Import ListNotations.

(* Precondition for common function *)
Definition problem_58_pre (l1 l2 : list Z) : Prop := True.

(* Specification of common function *)
Definition problem_58_spec (l1 l2 l_out: list Z) : Prop :=
  (forall x: Z, In x l_out <-> (In x l1 /\ In x l2)) /\
  Sorted Z.le l_out /\
  NoDup l_out.

(* Test case *)
Example test_common:
  problem_58_spec [1%Z; 4%Z; 3%Z; 34%Z; 653%Z; 2%Z; 5%Z]
                  [5%Z; 7%Z; 1%Z; 5%Z; 9%Z; 653%Z; 121%Z]
                  [1%Z; 5%Z; 653%Z].
Proof.
  unfold problem_58_spec. split.
  - intros x. simpl. split.
    + intros [H | [H | [H | H]]]; subst; auto; split; simpl; auto.
    + intros [H1 H2]. simpl in *. destruct H1 as [H1 | [H1 | [H1 | [H1 | [H1 | [H1 | H1]]]]]]; subst;
      destruct H2 as [H2 | [H2 | [H2 | [H2 | [H2 | [H2 | H2]]]]]]; subst; auto.
  - split.
    + repeat constructor; lia.
    + repeat constructor; intros H; inversion H.
Qed.