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

Lemma triple_nested_bracketed : is_correctly_bracketed ["("%char; "("%char; "("%char; ")"%char; ")"%char; ")"%char].
Proof.
  replace ["("%char; "("%char; "("%char; ")"%char; ")"%char; ")"%char]
    with ("("%char :: ["("%char; "("%char; ")"%char; ")"%char] ++ [")"%char]).
  - apply cb_nest.
    replace ["("%char; "("%char; ")"%char; ")"%char]
      with ("("%char :: ["("%char; ")"%char] ++ [")"%char]).
    + apply cb_nest.
      replace ["("%char; ")"%char] with ("("%char :: [] ++ [")"%char]).
      * apply cb_nest. apply cb_nil.
      * simpl. reflexivity.
    + simpl. reflexivity.
  - simpl. reflexivity.
Qed.

Example test_problem_61 : problem_61_spec ["("%char; "("%char; "("%char; ")"%char; ")"%char; ")"%char] true.
Proof.
  unfold problem_61_spec.
  split.
  - intros _. apply triple_nested_bracketed.
  - intros _. reflexivity.
Qed.