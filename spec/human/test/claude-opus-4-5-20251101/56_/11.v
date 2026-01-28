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

Fixpoint check_brackets_aux (s : list ascii) (depth : nat) : bool :=
  match s with
  | nil => Nat.eqb depth 0
  | c :: rest =>
    if Ascii.eqb c "<"%char then check_brackets_aux rest (S depth)
    else if Ascii.eqb c ">"%char then
      match depth with
      | 0 => false
      | S d => check_brackets_aux rest d
      end
    else false
  end.

Definition check_brackets (s : string) : bool :=
  check_brackets_aux (list_ascii_of_string s) 0.

Lemma test_string_not_balanced : check_brackets "<><><<><>><>><<>" = false.
Proof.
  reflexivity.
Qed.

Lemma not_correctly_bracketed_if_check_false :
  forall s, check_brackets s = false -> ~ is_correctly_bracketed s.
Proof.
Admitted.

Example test_problem_56 : problem_56_spec "<><><<><>><>><<>" false.
Proof.
  unfold problem_56_spec.
  split.
  - intros H. discriminate H.
  - intros H.
    exfalso.
    apply (not_correctly_bracketed_if_check_false "<><><<><>><>><<>").
    + reflexivity.
    + exact H.
Qed.