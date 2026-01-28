Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Strings.String.

Import ListNotations.
Open Scope string_scope.

(* Helper definitions *)
Definition is_space (c : ascii) : Prop := c = " "%char.

Inductive is_sorted : string -> Prop :=
  | sorted_nil : is_sorted ""
  | sorted_one : forall c, is_sorted (String c "")
  | sorted_cons : forall c1 c2 s',
      nat_of_ascii c1 <= nat_of_ascii c2 ->
      is_sorted (String c2 s') ->
      is_sorted (String c1 (String c2 s')).

Inductive SplitOnSpaces_aux_rel : string -> string -> list string -> Prop :=
  | sosar_nil_empty : forall current_group, current_group = "" -> SplitOnSpaces_aux_rel current_group "" []
  | sosar_nil_nonempty : forall current_group, current_group <> "" -> SplitOnSpaces_aux_rel current_group "" [current_group]
  | sosar_space_empty : forall current_group h t result,
      is_space h ->
      current_group = "" ->
      SplitOnSpaces_aux_rel "" t result ->
      SplitOnSpaces_aux_rel current_group (String h t) result
  | sosar_space_nonempty : forall current_group h t result,
      is_space h ->
      current_group <> "" ->
      SplitOnSpaces_aux_rel "" t result ->
      SplitOnSpaces_aux_rel current_group (String h t) (current_group :: result)
  | sosar_char : forall current_group h t result,
      ~ is_space h ->
      SplitOnSpaces_aux_rel (current_group ++ String h "") t result ->
      SplitOnSpaces_aux_rel current_group (String h t) result.

Inductive SplitOnSpaces_rel : string -> list string -> Prop :=
  | sos_base : forall s result, SplitOnSpaces_aux_rel "" s result -> SplitOnSpaces_rel s result.

Fixpoint list_ascii_of_string (s : string) : list ascii :=
  match s with
  | EmptyString => []
  | String c s' => c :: list_ascii_of_string s'
  end.

Definition problem_86_spec (s s_out : string) : Prop :=
  String.length s = String.length s_out /\
  (forall i, i < String.length s ->
    forall c1 c2,
      String.get i s = Some c1 ->
      String.get i s_out = Some c2 ->
      (is_space c1 <-> is_space c2)) /\
  (exists words_in words_out,
    SplitOnSpaces_rel s words_in /\
    SplitOnSpaces_rel s_out words_out /\
    Forall2 (fun w_in w_out => Permutation (list_ascii_of_string w_in) (list_ascii_of_string w_out) /\ is_sorted w_out) words_in words_out).

(* Helper lemmas *)
Lemma list_ascii_of_string_singleton : forall c,
  list_ascii_of_string (String c EmptyString) = [c].
Proof.
  intros c. simpl. reflexivity.
Qed.

Lemma is_sorted_singleton : forall c, is_sorted (String c EmptyString).
Proof.
  intros c. apply sorted_one.
Qed.

Lemma Permutation_refl_singleton : forall (A : Type) (c : A),
  Permutation [c] [c].
Proof.
  intros A c. apply Permutation_refl.
Qed.

(* Test case proof *)
Example anti_shuffle_Hi : problem_86_spec "Hi" "Hi".
Proof.
  unfold problem_86_spec.
  split. 
  - simpl. reflexivity.
  split.
  - intros i Hlen c1 c2 Hget1 Hget2.
    unfold is_space.
    assert (Hi_length: String.length "Hi" = 2) by reflexivity.
    simpl in Hlen.
    destruct i as [|i].
    + inversion Hget1. inversion Hget2.
      split; intro H; assumption.
    + destruct i as [|i].
      * inversion Hget1. inversion Hget2.
        split; intro H; assumption.
      * simpl in Hlen. lia.
  - exists ["Hi"], ["Hi"].
    split.
    + apply sos_base.
      apply sosar_char with (h:="H"%char).
      * intro H. unfold is_space in H. discriminate.
      * apply sosar_char with (h:="i"%char).
        { intro H. unfold is_space in H. discriminate. }
        apply sosar_nil_nonempty.
        intro H. inversion H.
    + split.
      * apply sos_base.
        apply sosar_char with (h:="H"%char).
        { intro H. unfold is_space in H. discriminate. }
        apply sosar_char with (h:="i"%char).
        { intro H. unfold is_space in H. discriminate. }
        apply sosar_nil_nonempty.
        intro H. inversion H.
      * apply Forall2_cons.
        { split.
          - rewrite list_ascii_of_string_singleton.
            rewrite list_ascii_of_string_singleton.
            apply Permutation_refl_singleton.
          - apply is_sorted_singleton. }
        apply Forall2_nil.
Qed.