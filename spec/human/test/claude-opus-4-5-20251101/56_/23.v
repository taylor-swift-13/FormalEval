Require Import Coq.Lists.List.
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Open Scope string_scope.

Inductive is_correctly_bracketed : string -> Prop :=
  | cb_nil    : is_correctly_bracketed ""
  | cb_nest   : forall l,
                  is_correctly_bracketed l ->
                  is_correctly_bracketed ("<" ++ l ++ ">")
  | cb_concat : forall l1 l2,
                  is_correctly_bracketed l1 ->
                  is_correctly_bracketed l2 ->
                  is_correctly_bracketed (l1 ++ l2).

Definition problem_56_pre (brackets : string) : Prop :=
    Forall (fun c => c = "<"%char \/ c = ">"%char) (list_ascii_of_string brackets).

Definition problem_56_spec (brackets : string) (b : bool) : Prop :=
  b = true <-> is_correctly_bracketed brackets.

Lemma angle_brackets_correct : is_correctly_bracketed "<>".
Proof.
  assert (H: "<>" = "<" ++ "" ++ ">").
  { reflexivity. }
  rewrite H.
  apply cb_nest.
  apply cb_nil.
Qed.

Lemma double_angle_correct : is_correctly_bracketed "<<>>".
Proof.
  assert (H: "<<>>" = "<" ++ "<>" ++ ">").
  { reflexivity. }
  rewrite H.
  apply cb_nest.
  apply angle_brackets_correct.
Qed.

Lemma triple_angle_correct : is_correctly_bracketed "<<<>>>".
Proof.
  assert (H: "<<<>>>" = "<" ++ "<<>>" ++ ">").
  { reflexivity. }
  rewrite H.
  apply cb_nest.
  apply double_angle_correct.
Qed.

Lemma nested_example_correct : is_correctly_bracketed "<<<>><>>".
Proof.
  assert (H: "<<<>><>>" = "<" ++ "<<>><>" ++ ">").
  { reflexivity. }
  rewrite H.
  apply cb_nest.
  assert (H2: "<<>><>" = "<<>>" ++ "<>").
  { reflexivity. }
  rewrite H2.
  apply cb_concat.
  - apply double_angle_correct.
  - apply angle_brackets_correct.
Qed.

Lemma outer_nested_correct : is_correctly_bracketed "<<<<>><>>>".
Proof.
  assert (H: "<<<<>><>>>" = "<" ++ "<<<>><>>" ++ ">").
  { reflexivity. }
  rewrite H.
  apply cb_nest.
  apply nested_example_correct.
Qed.

Lemma full_example_correct : is_correctly_bracketed "<<<<>><>>><>".
Proof.
  assert (H: "<<<<>><>>><>" = "<<<<>><>>>" ++ "<>").
  { reflexivity. }
  rewrite H.
  apply cb_concat.
  - apply outer_nested_correct.
  - apply angle_brackets_correct.
Qed.

Example test_problem_56 : problem_56_spec "<<<<>><>>><>" true.
Proof.
  unfold problem_56_spec.
  split.
  - intros _. apply full_example_correct.
  - intros _. reflexivity.
Qed.