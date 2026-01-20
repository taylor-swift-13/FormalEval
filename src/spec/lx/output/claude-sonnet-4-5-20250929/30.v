Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Import ListNotations.
Open Scope R_scope.

Inductive is_subsequence {A : Type} : list A -> list A -> Prop :=
  | sub_nil : is_subsequence [] []
  | sub_cons_hd : forall x l1 l2, is_subsequence l1 l2 -> is_subsequence (x :: l1) (x :: l2)
  | sub_cons_tl : forall x l1 l2, is_subsequence l1 l2 -> is_subsequence l1 (x :: l2).

Definition is_positive (r : R) : Prop :=
  r > 0.

Definition Spec (input : list R) (output : list R) : Prop :=
  is_subsequence output input /\
  (forall r, In r output <-> (In r input /\ is_positive r)).

Example test_get_positive :
  Spec [(-1); (-2); 4; 5; 6] [4; 5; 6].
Proof.
  unfold Spec.
  split.
  - apply sub_cons_tl.
    apply sub_cons_tl.
    apply sub_cons_hd.
    apply sub_cons_hd.
    apply sub_cons_hd.
    apply sub_nil.
  - intro r.
    split.
    + intro H.
      simpl in H.
      destruct H as [H1 | [H2 | [H3 | H4]]].
      * subst.
        split.
        -- simpl. right. right. left. reflexivity.
        -- unfold is_positive. lra.
      * subst.
        split.
        -- simpl. right. right. right. left. reflexivity.
        -- unfold is_positive. lra.
      * subst.
        split.
        -- simpl. right. right. right. right. left. reflexivity.
        -- unfold is_positive. lra.
      * contradiction.
    + intro H.
      destruct H as [H_in H_pos].
      simpl in H_in.
      destruct H_in as [H1 | [H2 | [H3 | [H4 | [H5 | H6]]]]].
      * subst.
        unfold is_positive in H_pos.
        lra.
      * subst.
        unfold is_positive in H_pos.
        lra.
      * subst.
        simpl. left. reflexivity.
      * subst.
        simpl. right. left. reflexivity.
      * subst.
        simpl. right. right. left. reflexivity.
      * contradiction.
Qed.