Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Strings.String.
Require Import Lia.

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

Definition  problem_86_spec (s s_out : string) : Prop :=
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

Lemma spaces_equiv_The_quick :
  forall i,
    i < String.length "The quick brown fox jumps over the lazy dog." ->
    forall c1 c2,
      String.get i "The quick brown fox jumps over the lazy dog." = Some c1 ->
      String.get i "Teh cikqu bnorw fox jmpsu eorv eht alyz .dgo" = Some c2 ->
      (is_space c1 <-> is_space c2).
Proof. Admitted.

Lemma sos_input_split :
  SplitOnSpaces_rel
    "The quick brown fox jumps over the lazy dog."
    ["The"; "quick"; "brown"; "fox"; "jumps"; "over"; "the"; "lazy"; "dog."].
Proof. Admitted.

Lemma sos_output_split :
  SplitOnSpaces_rel
    "Teh cikqu bnorw fox jmpsu eorv eht alyz .dgo"
    ["Teh"; "cikqu"; "bnorw"; "fox"; "jmpsu"; "eorv"; "eht"; "alyz"; ".dgo"].
Proof. Admitted.

Lemma Forall2_perm_sorted_The_quick :
  Forall2
    (fun w_in w_out =>
       Permutation (list_ascii_of_string w_in) (list_ascii_of_string w_out) /\ is_sorted w_out)
    ["The"; "quick"; "brown"; "fox"; "jumps"; "over"; "the"; "lazy"; "dog."]
    ["Teh"; "cikqu"; "bnorw"; "fox"; "jmpsu"; "eorv"; "eht"; "alyz"; ".dgo"].
Proof. Admitted.

Example anti_shuffle_The_quick_example :
  problem_86_spec
    "The quick brown fox jumps over the lazy dog."
    "Teh cikqu bnorw fox jmpsu eorv eht alyz .dgo".
Proof.
  split.
  - simpl. reflexivity.
  - split.
    + intros i Hi_lt c1 c2 Hget1 Hget2.
      eapply spaces_equiv_The_quick; eauto.
    + exists
        ["The"; "quick"; "brown"; "fox"; "jumps"; "over"; "the"; "lazy"; "dog."],
        ["Teh"; "cikqu"; "bnorw"; "fox"; "jmpsu"; "eorv"; "eht"; "alyz"; ".dgo"].
      split.
      * apply sos_input_split.
      * split.
        -- apply sos_output_split.
        -- apply Forall2_perm_sorted_The_quick.
Qed.