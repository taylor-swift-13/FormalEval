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

(* Helper lemmas for positive numbers *)
Lemma pos_4 : IZR 4 > 0.
Proof.
  unfold Rgt.
  apply (IZR_lt 0 4).
  lia.
Qed.

Lemma pos_5 : IZR 5 > 0.
Proof.
  unfold Rgt.
  apply (IZR_lt 0 5).
  lia.
Qed.

Lemma pos_6 : IZR 6 > 0.
Proof.
  unfold Rgt.
  apply (IZR_lt 0 6).
  lia.
Qed.

Lemma neg_1 : ~ (IZR (-1) > 0).
Proof.
  unfold Rgt.
  intro H.
  apply (Rlt_asym 0 (IZR (-1))).
  - exact H.
  - apply (IZR_lt (-1) 0). lia.
Qed.

Lemma neg_2 : ~ (IZR (-2) > 0).
Proof.
  unfold Rgt.
  intro H.
  apply (Rlt_asym 0 (IZR (-2))).
  - exact H.
  - apply (IZR_lt (-2) 0). lia.
Qed.

Example test_problem_30 :
  let input := [IZR (-1); IZR (-2); IZR 4; IZR 5; IZR 6] in
  let output := [IZR 4; IZR 5; IZR 6] in
  problem_30_spec input output.
Proof.
  unfold problem_30_spec, is_positive.
  simpl.
  split.
  - (* is_subsequence *)
    apply sub_cons_skip.
    apply sub_cons_skip.
    apply sub_cons_match.
    apply sub_cons_match.
    apply sub_cons_match.
    apply sub_nil.
  - (* forall r, In r output <-> (In r input /\ r > 0) *)
    intro r.
    split.
    + (* In r output -> In r input /\ r > 0 *)
      intro H.
      destruct H as [H | [H | [H | H]]].
      * rewrite H. split.
        -- right. right. left. reflexivity.
        -- exact pos_4.
      * rewrite H. split.
        -- right. right. right. left. reflexivity.
        -- exact pos_5.
      * rewrite H. split.
        -- right. right. right. right. left. reflexivity.
        -- exact pos_6.
      * contradiction.
    + (* In r input /\ r > 0 -> In r output *)
      intro H.
      destruct H as [Hin Hpos].
      destruct Hin as [H | [H | [H | [H | [H | H]]]]].
      * rewrite H in Hpos. exfalso. apply neg_1. exact Hpos.
      * rewrite H in Hpos. exfalso. apply neg_2. exact Hpos.
      * rewrite H. left. reflexivity.
      * rewrite H. right. left. reflexivity.
      * rewrite H. right. right. left. reflexivity.
      * contradiction.
Qed.