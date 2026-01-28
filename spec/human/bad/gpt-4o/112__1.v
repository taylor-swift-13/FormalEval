Require Import Coq.Lists.List Coq.Strings.Ascii Coq.Strings.String Coq.Bool.Bool.
Import ListNotations.

Inductive exists_in_list {A : Type} : A -> list A -> Prop :=
| eil_head : forall x xs, exists_in_list x (x :: xs)
| eil_tail : forall x y xs, exists_in_list x xs -> exists_in_list x (y :: xs).

Inductive delete_chars_rel : list ascii -> list ascii -> list ascii -> Prop :=
| dcr_nil : forall c, delete_chars_rel nil c nil
| dcr_delete : forall h t c res, exists_in_list h c ->
    delete_chars_rel t c res ->
    delete_chars_rel (h :: t) c res
| dcr_keep : forall h t c res, ~ exists_in_list h c ->
    delete_chars_rel t c res ->
    delete_chars_rel (h :: t) c (h :: res).

Inductive is_pal_rel : list ascii -> Prop :=
| ipr_nil : is_pal_rel nil
| ipr_single : forall c, is_pal_rel [c]
| ipr_pair : forall c s, is_pal_rel s -> is_pal_rel (c :: (s ++ [c])).

Fixpoint list_ascii_of_string (s : string) : list ascii :=
  match s with
  | EmptyString => []
  | String a s' => a :: list_ascii_of_string s'
  end.

Fixpoint string_of_list_ascii (l : list ascii) : string :=
  match l with
  | [] => EmptyString
  | a :: l' => String a (string_of_list_ascii l')
  end.

Lemma list_ascii_of_string_inv : forall s,
  string_of_list_ascii (list_ascii_of_string s) = s.
Proof.
  intros s. induction s as [| a s' IH].
  - reflexivity.
  - simpl. rewrite IH. reflexivity.
Qed.

Definition problem_112_spec (s c : string) (output : string * bool) : Prop :=
  let '(res, is_pal) := output in
  let ls := list_ascii_of_string s in
  let lc := list_ascii_of_string c in
  let lres := list_ascii_of_string res in
  delete_chars_rel ls lc lres /\
  (is_pal = true <-> is_pal_rel lres).

Example example_1 : problem_112_spec "abcde" "ae" ("bcd", false).
Proof.
  unfold problem_112_spec.
  simpl. split.
  - (* Proving delete_chars_rel *)
    apply dcr_keep.
    + intros H. inversion H; subst; inversion H1.
    + apply dcr_keep.
      * intros H. inversion H; subst; inversion H1.
      * apply dcr_keep.
        { intros H. inversion H; subst; inversion H1. }
        { apply dcr_nil. }
  - (* Proving is_pal = false <-> is_pal_rel ["b"; "c"; "d"] *)
    split.
    + intros H. inversion H.
    + intros H. inversion H; subst. inversion H2; subst. inversion H3; subst.
Qed.