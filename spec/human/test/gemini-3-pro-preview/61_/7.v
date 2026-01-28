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

Example test_case_1 : problem_61_spec ["("%char] false.
Proof.
  unfold problem_61_spec.
  split.
  - intros H. inversion H.
  - intros H.
    remember ["("%char] as s.
    induction H.
    + discriminate.
    + injection Heqs as Heqs.
      destruct l; simpl in Heqs; discriminate.
    + destruct l1.
      * simpl in Heqs. subst l2.
        apply IHis_correctly_bracketed2. reflexivity.
      * simpl in Heqs. injection Heqs as Ha Hl. subst a.
        destruct l1.
        -- simpl in Hl. subst l2.
           apply IHis_correctly_bracketed1. reflexivity.
        -- simpl in Hl. discriminate.
Qed.