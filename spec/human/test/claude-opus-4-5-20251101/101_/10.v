Require Import Coq.Strings.Ascii Coq.Strings.String Coq.Lists.List.
Import ListNotations.

Inductive is_delimiter : ascii -> Prop :=
| id_comma : is_delimiter ","%char
| id_space : is_delimiter " "%char.

Inductive words_string_aux_rel : list ascii -> list ascii -> list (list ascii) -> Prop :=
| wsar_empty_empty : words_string_aux_rel nil nil nil
| wsar_empty_word : forall cur_word, cur_word <> nil ->
   words_string_aux_rel nil cur_word (cur_word :: nil)
| wsar_delim_empty : forall c cs words, is_delimiter c ->
   words_string_aux_rel cs nil words ->
   words_string_aux_rel (c :: cs) nil words
| wsar_delim_word : forall c cs cur_word words, is_delimiter c -> cur_word <> nil ->
   words_string_aux_rel cs nil words ->
   words_string_aux_rel (c :: cs) cur_word (cur_word :: words)
| wsar_char_extend : forall c cs cur_word words, ~ is_delimiter c ->
   words_string_aux_rel cs (cur_word ++ [c]) words ->
   words_string_aux_rel (c :: cs) cur_word words.

Inductive words_string_rel : list ascii -> list (list ascii) -> Prop :=
| wsr_build : forall s output, words_string_aux_rel s nil output ->
   words_string_rel s output.

Definition problem_101_pre (s : string) : Prop :=
  let l := list_ascii_of_string s in
  Forall (fun c =>
    let n := nat_of_ascii c in
      (65 <= n /\ n <= 90) \/ (97 <= n /\ n <= 122) \/ c = ","%char \/ c = " "%char) l.

Definition problem_101_spec (s : string) (output : list string) : Prop :=
  exists output_list_ascii,
    words_string_rel (list_ascii_of_string s) output_list_ascii /\
    output = map string_of_list_ascii output_list_ascii.

Lemma not_delim_H : ~ is_delimiter "H"%char.
Proof. intro H. inversion H. Qed.

Lemma not_delim_i : ~ is_delimiter "i"%char.
Proof. intro H. inversion H. Qed.

Lemma not_delim_t : ~ is_delimiter "t"%char.
Proof. intro H. inversion H. Qed.

Lemma not_delim_h : ~ is_delimiter "h"%char.
Proof. intro H. inversion H. Qed.

Lemma not_delim_e : ~ is_delimiter "e"%char.
Proof. intro H. inversion H. Qed.

Lemma not_delim_r : ~ is_delimiter "r"%char.
Proof. intro H. inversion H. Qed.

Lemma not_delim_s : ~ is_delimiter "s"%char.
Proof. intro H. inversion H. Qed.

Lemma not_delim_a : ~ is_delimiter "a"%char.
Proof. intro H. inversion H. Qed.

Lemma not_delim_l : ~ is_delimiter "l"%char.
Proof. intro H. inversion H. Qed.

Lemma not_delim_o : ~ is_delimiter "o"%char.
Proof. intro H. inversion H. Qed.

Lemma not_delim_f : ~ is_delimiter "f"%char.
Proof. intro H. inversion H. Qed.

Lemma not_delim_p : ~ is_delimiter "p"%char.
Proof. intro H. inversion H. Qed.

Lemma not_delim_c : ~ is_delimiter "c"%char.
Proof. intro H. inversion H. Qed.

Lemma list_not_nil : forall {A : Type} (x : A) (xs : list A), x :: xs <> nil.
Proof. intros. discriminate. Qed.

Example test_words_string :
  problem_101_spec "Hi,there is,a lot,of,space   ,     ,"%string 
    ("Hi"%string :: "there"%string :: "is"%string :: "a"%string :: "lot"%string :: "of"%string :: "space"%string :: nil).
Proof.
  unfold problem_101_spec.
  exists (("H"%char :: "i"%char :: nil) :: 
          ("t"%char :: "h"%char :: "e"%char :: "r"%char :: "e"%char :: nil) :: 
          ("i"%char :: "s"%char :: nil) :: 
          ("a"%char :: nil) :: 
          ("l"%char :: "o"%char :: "t"%char :: nil) :: 
          ("o"%char :: "f"%char :: nil) :: 
          ("s"%char :: "p"%char :: "a"%char :: "c"%char :: "e"%char :: nil) :: nil).
  split.
  - constructor.
    simpl.
    apply wsar_char_extend. { apply not_delim_H. } simpl.
    apply wsar_char_extend. { apply not_delim_i. } simpl.
    apply wsar_delim_word. { constructor. } { apply list_not_nil. }
    apply wsar_char_extend. { apply not_delim_t. } simpl.
    apply wsar_char_extend. { apply not_delim_h. } simpl.
    apply wsar_char_extend. { apply not_delim_e. } simpl.
    apply wsar_char_extend. { apply not_delim_r. } simpl.
    apply wsar_char_extend. { apply not_delim_e. } simpl.
    apply wsar_delim_word. { constructor. } { apply list_not_nil. }
    apply wsar_char_extend. { apply not_delim_i. } simpl.
    apply wsar_char_extend. { apply not_delim_s. } simpl.
    apply wsar_delim_word. { constructor. } { apply list_not_nil. }
    apply wsar_char_extend. { apply not_delim_a. } simpl.
    apply wsar_delim_word. { constructor. } { apply list_not_nil. }
    apply wsar_char_extend. { apply not_delim_l. } simpl.
    apply wsar_char_extend. { apply not_delim_o. } simpl.
    apply wsar_char_extend. { apply not_delim_t. } simpl.
    apply wsar_delim_word. { constructor. } { apply list_not_nil. }
    apply wsar_char_extend. { apply not_delim_o. } simpl.
    apply wsar_char_extend. { apply not_delim_f. } simpl.
    apply wsar_delim_word. { constructor. } { apply list_not_nil. }
    apply wsar_char_extend. { apply not_delim_s. } simpl.
    apply wsar_char_extend. { apply not_delim_p. } simpl.
    apply wsar_char_extend. { apply not_delim_a. } simpl.
    apply wsar_char_extend. { apply not_delim_c. } simpl.
    apply wsar_char_extend. { apply not_delim_e. } simpl.
    apply wsar_delim_word. { constructor. } { apply list_not_nil. }
    apply wsar_delim_empty. { constructor. }
    apply wsar_delim_empty. { constructor. }
    apply wsar_delim_empty. { constructor. }
    apply wsar_delim_empty. { constructor. }
    apply wsar_delim_empty. { constructor. }
    apply wsar_delim_empty. { constructor. }
    apply wsar_delim_empty. { constructor. }
    apply wsar_delim_empty. { constructor. }
    apply wsar_delim_empty. { constructor. }
    apply wsar_empty_empty.
  - reflexivity.
Qed.