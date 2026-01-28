Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import Coq.Reals.RIneq.
Import ListNotations.
Open Scope R_scope.

Inductive is_subsequence {A : Type} : list A -> list A -> Prop :=
  | sub_nil : forall l, is_subsequence [] l
  | sub_cons_match : forall x l1 l2, is_subsequence l1 l2 -> is_subsequence (x :: l1) (x :: l2)
  | sub_cons_skip : forall x l1 l2, is_subsequence l1 l2 -> is_subsequence l1 (x :: l2).

Definition is_positive (r : R) : Prop := r > 0.

Definition problem_30_spec (input : list R) (output : list R) : Prop :=
  is_subsequence output input /\
  (forall r, In r output <-> (In r input /\ is_positive r)).

Lemma pos_4 : 4 > 0. Proof. lra. Qed.
Lemma pos_5 : 5 > 0. Proof. lra. Qed.
Lemma pos_6 : 6 > 0. Proof. lra. Qed.
Lemma neg_1 : ~(-1 > 0). Proof. lra. Qed.
Lemma neg_2 : ~(-2 > 0). Proof. lra. Qed.

Example test_case_proof : 
  problem_30_spec [(-1)%R; (-2)%R; 4%R; 5%R; 6%R] [4%R; 5%R; 6%R].
Proof.
  unfold problem_30_spec.
  split.
  - (* Prove is_subsequence *)
    apply sub_cons_skip with (x := (-1)%R).
    apply sub_cons_skip with (x := (-2)%R).
    apply sub_cons_match.
    apply sub_cons_match.
    apply sub_cons_match.
    apply sub_nil.
  - (* Prove the equivalence *)
    intro r.
    split.
    + intro H.
      split.
      * (* Prove In r input *)
        simpl in H.
        destruct H as [H | [H | [H | H]]].
        { simpl. right. right. left. assumption. }
        { simpl. right. right. right. left. assumption. }
        { simpl. right. right. right. right. left. assumption. }
        { contradiction. }
      * (* Prove is_positive r *)
        simpl in H.
        destruct H as [H | [H | [H | H]]].
        { unfold is_positive. apply pos_4. }
        { unfold is_positive. apply pos_5. }
        { unfold is_positive. apply pos_6. }
        { contradiction. }
    + intro H.
      destruct H as [Hin Hpos].
      simpl in Hin.
      destruct Hin as [H | [H | [H | [H | H]]]].
      * (* Case r = -1 *)
        exfalso. apply neg_1. unfold is_positive in Hpos. apply Hpos.
      * (* Case r = -2 *)
        exfalso. apply neg_2. unfold is_positive in Hpos. apply Hpos.
      * (* Case r = 4 *)
        simpl. left. assumption.
      * (* Case r = 5 *)
        simpl. right. left. assumption.
      * (* Case r = 6 *)
        simpl. right. right. left. assumption.
Qed.