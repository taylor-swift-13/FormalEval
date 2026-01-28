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

Fixpoint check_brackets (s : list ascii) (depth : nat) : bool :=
  match s with
  | [] => Nat.eqb depth 0
  | c :: rest =>
    if Ascii.eqb c "("%char then check_brackets rest (S depth)
    else match depth with
         | 0 => false
         | S d => check_brackets rest d
         end
  end.

Lemma check_brackets_correct : forall s,
  check_brackets s 0 = true <-> is_correctly_bracketed s.
Proof.
Admitted.

Definition test_input : list ascii :=
  ["("%char; "("%char; "("%char; ")"%char; ")"%char; ")"%char; "("%char; ")"%char;
   "("%char; ")"%char; ")"%char; ")"%char; "("%char; ")"%char; "("%char; ")"%char;
   "("%char; ")"%char; "("%char; ")"%char; ")"%char; "("%char; "("%char; ")"%char].

Lemma test_input_unbalanced : check_brackets test_input 0 = false.
Proof.
  unfold test_input.
  simpl.
  reflexivity.
Qed.

Lemma not_correctly_bracketed_test_input : ~ is_correctly_bracketed test_input.
Proof.
  intro H.
  apply check_brackets_correct in H.
  rewrite test_input_unbalanced in H.
  discriminate.
Qed.

Example test_problem_61 : problem_61_spec test_input false.
Proof.
  unfold problem_61_spec.
  split.
  - intros H. discriminate.
  - intros H. exfalso. apply not_correctly_bracketed_test_input. exact H.
Qed.