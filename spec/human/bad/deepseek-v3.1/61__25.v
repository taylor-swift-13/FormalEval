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

Lemma list_eq : "("%char :: [] ++ [")"%char] = ["("%char; ")"%char].
Proof. reflexivity. Qed.

Example test_case_2 : problem_61_spec [")"%char; ")"%char; "("%char] false.
Proof.
  unfold problem_61_spec.
  split.
  - intros H.
    (* In this case, the input list has an extra closing bracket at the start, so it cannot be correctly bracketed *)
    intros H_bracketed.
    destruct H_bracketed as [H_nil | [H_nest | H_concat]].
    + inversion H_nil.
    + inversion H_nest.
    + inversion H_concat; subst.
      destruct l1; simpl in *; try discriminate.
      destruct l2; simpl in *; try discriminate.
    Qed.
  - intros H. reflexivity.
Qed.