Require Import Coq.Lists.List.
Require Import Coq.Strings.Ascii Coq.Strings.String.
Import ListNotations.

Inductive is_correctly_bracketed : list ascii -> Prop :=
  | cb_nil    : is_correctly_bracketed []
  | cb_nest   : forall l,
                  is_correctly_bracketed l ->
                  is_correctly_bracketed ("("%char :: l ++ [")"%char])
  | cb_concat : forall l1 l2,
                  is_correctly_bracketed l1 ->
                  is_correctly_bracketed l2 ->
                  is_correctly_bracketed (l1 ++ l2).

Definition problem_61_pre (brackets : string) : Prop :=
  Forall (fun c => c = "("%char \/ c = ")"%char) (list_ascii_of_string brackets).

Definition problem_61_spec (brackets : list ascii) (b : bool) : Prop :=
  b = true <-> is_correctly_bracketed brackets.

Lemma not_bracketed_single_close : ~ is_correctly_bracketed [")"%char].
Proof.
  intro H.
  remember [")"%char] as l eqn:Heq.
  induction H.
  - discriminate Heq.
  - destruct l.
    + simpl in Heq. discriminate Heq.
    + simpl in Heq. injection Heq. intros H1 H2. discriminate H2.
  - destruct l1.
    + simpl in Heq. apply IHis_correctly_bracketed2. exact Heq.
    + simpl in Heq. injection Heq. intros H1 H2.
      inversion H_.
      * destruct l1; discriminate.
      * destruct l; simpl in H2; discriminate H2.
      * destruct l0.
        -- simpl in H2. subst. apply IHis_correctly_bracketed2. 
           destruct l2; [reflexivity | destruct l2; simpl in H1; discriminate].
        -- simpl in H2. discriminate H2.
Qed.

Example test_problem_61 : problem_61_spec [")"%char] false.
Proof.
  unfold problem_61_spec.
  split.
  - intros H. discriminate H.
  - intros H. exfalso. apply not_bracketed_single_close. exact H.
Qed.