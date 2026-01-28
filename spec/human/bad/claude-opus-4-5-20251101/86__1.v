Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Strings.String.
Require Import Coq.Arith.PeanoNat.

Import ListNotations.
Open Scope string_scope.

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

Definition problem_86_pre (s : string) : Prop := True.

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

Lemma H_not_space : ~ is_space "H"%char.
Proof.
  unfold is_space. intro H.
  discriminate H.
Qed.

Lemma i_not_space : ~ is_space "i"%char.
Proof.
  unfold is_space. intro H.
  discriminate H.
Qed.

Lemma split_Hi : SplitOnSpaces_rel "Hi" ["Hi"].
Proof.
  apply sos_base.
  apply sosar_char.
  - apply H_not_space.
  - simpl.
    apply sosar_char.
    + apply i_not_space.
    + simpl.
      apply sosar_nil_nonempty.
      discriminate.
Qed.

Lemma Hi_sorted : is_sorted "Hi".
Proof.
  apply sorted_cons.
  - simpl. apply le_S. apply le_S. apply le_S. apply le_S. apply le_S.
    apply le_S. apply le_S. apply le_S. apply le_S. apply le_S.
    apply le_S. apply le_S. apply le_S. apply le_S. apply le_S.
    apply le_S. apply le_S. apply le_S. apply le_S. apply le_S.
    apply le_S. apply le_n.
  - apply sorted_one.
Qed.

Lemma Hi_perm : Permutation (list_ascii_of_string "Hi") (list_ascii_of_string "Hi").
Proof.
  simpl. apply Permutation_refl.
Qed.

Example test_anti_shuffle_Hi : problem_86_spec "Hi" "Hi".
Proof.
  unfold problem_86_spec.
  split.
  - reflexivity.
  - split.
    + intros i Hi_lt c1 c2 Hget1 Hget2.
      split; intro Hspace.
      * destruct i.
        -- simpl in Hget1, Hget2.
           injection Hget1 as Hc1.
           injection Hget2 as Hc2.
           rewrite <- Hc1, <- Hc2.
           exact Hspace.
        -- destruct i.
           ++ simpl in Hget1, Hget2.
              injection Hget1 as Hc1.
              injection Hget2 as Hc2.
              rewrite <- Hc1, <- Hc2.
              exact Hspace.
           ++ simpl in Hi_lt. 
              apply Nat.succ_lt_mono in Hi_lt.
              apply Nat.succ_lt_mono in Hi_lt.
              inversion Hi_lt.
      * destruct i.
        -- simpl in Hget1, Hget2.
           injection Hget1 as Hc1.
           injection Hget2 as Hc2.
           rewrite <- Hc1, <- Hc2.
           exact Hspace.
        -- destruct i.
           ++ simpl in Hget1, Hget2.
              injection Hget1 as Hc1.
              injection Hget2 as Hc2.
              rewrite <- Hc1, <- Hc2.
              exact Hspace.
           ++ simpl in Hi_lt.
              apply Nat.succ_lt_mono in Hi_lt.
              apply Nat.succ_lt_mono in Hi_lt.
              inversion Hi_lt.
    + exists ["Hi"], ["Hi"].
      split.
      * apply split_Hi.
      * split.
        -- apply split_Hi.
        -- apply Forall2_cons.
           ++ split.
              ** apply Hi_perm.
              ** apply Hi_sorted.
           ++ apply Forall2_nil.
Qed.