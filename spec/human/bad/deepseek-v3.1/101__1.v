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
   words_string_aux_rel (c :: cs) nil (cur_word :: words)
| wsar_char_extend : forall c cs cur_word words, ~ is_delimiter c ->
   words_string_aux_rel cs (cur_word ++ [c]) words ->
   words_string_aux_rel (c :: cs) cur_word words.

Inductive words_string_rel : list ascii -> list (list ascii) -> Prop :=
| wsr_build : forall s output, words_string_aux_rel s nil output ->
   words_string_rel s output.

(* 输入为仅包含字母、逗号或空格的字符列表 *)
Definition problem_101_pre (s : string) : Prop :=
  let l := list_ascii_of_string s in
  Forall (fun c =>
    let n := nat_of_ascii c in
      (65 <= n /\ n <= 90) \/ (97 <= n /\ n <= 122) \/ c = ","%char \/ c = " "%char) l.

Definition problem_101_spec (s : string) (output : list string) : Prop :=
  exists output_list_ascii,
    words_string_rel (list_ascii_of_string s) output_list_ascii /\
    output = map string_of_list_ascii output_list_ascii.

Lemma not_delimiter_H : ~ is_delimiter "H"%char.
Proof. unfold not; intros H; inversion H. Qed.

Lemma not_delimiter_i : ~ is_delimiter "i"%char.
Proof. unfold not; intros H; inversion H. Qed.

Lemma not_delimiter_m : ~ is_delimiter "m"%char.
Proof. unfold not; intros H; inversion H. Qed.

Lemma not_delimiter_y : ~ is_delimiter "y"%char.
Proof. unfold not; intros H; inversion H. Qed.

Lemma not_delimiter_n : ~ is_delimiter "n"%char.
Proof. unfold not; intros H; inversion H. Qed.

Lemma not_delimiter_a : ~ is_delimiter "a"%char.
Proof. unfold not; intros H; inversion H. Qed.

Lemma not_delimiter_e : ~ is_delimiter "e"%char.
Proof. unfold not; intros H; inversion H. Qed.

Lemma not_delimiter_s : ~ is_delimiter "s"%char.
Proof. unfold not; intros H; inversion H. Qed.

Lemma not_delimiter_J : ~ is_delimiter "J"%char.
Proof. unfold not; intros H; inversion H. Qed.

Lemma not_delimiter_o : ~ is_delimiter "o"%char.
Proof. unfold not; intros H; inversion H. Qed.

Lemma not_delimiter_h : ~ is_delimiter "h"%char.
Proof. unfold not; intros H; inversion H. Qed.

Example words_string_example : 
  problem_101_spec "Hi, my name is John" ["Hi"; "my"; "name"; "is"; "John"].
Proof.
  unfold problem_101_spec.
  exists [["H"; "i"]%char; ["m"; "y"]%char; ["n"; "a"; "m"; "e"]%char; ["i"; "s"]%char; ["J"; "o"; "h"; "n"]%char].
  split.
  - apply wsr_build.
    (* Process "Hi, my name is John" *)
    eapply wsar_char_extend.
    + apply not_delimiter_H.
    + eapply wsar_char_extend.
      * apply not_delimiter_i.
      * eapply wsar_delim_word.
        { apply id_comma. }
        { unfold not; intros H1; inversion H1. }
        { eapply wsar_delim_empty.
          { apply id_space. }
          { eapply wsar_char_extend.
            { apply not_delimiter_m. }
            { eapply wsar_char_extend.
              { apply not_delimiter_y. }
              { eapply wsar_delim_empty.
                { apply id_space. }
                { eapply wsar_char_extend.
                  { apply not_delimiter_n. }
                  { eapply wsar_char_extend.
                    { apply not_delimiter_a. }
                    { eapply wsar_char_extend.
                      { apply not_delimiter_m. }
                      { eapply wsar_char_extend.
                        { apply not_delimiter_e. }
                        { eapply wsar_delim_empty.
                          { apply id_space. }
                          { eapply wsar_char_extend.
                            { apply not_delimiter_i. }
                            { eapply wsar_char_extend.
                              { apply not_delimiter_s. }
                              { eapply wsar_delim_empty.
                                { apply id_space. }
                                { eapply wsar_char_extend.
                                  { apply not_delimiter_J. }
                                  { eapply wsar_char_extend.
                                    { apply not_delimiter_o. }
                                    { eapply wsar_char_extend.
                                      { apply not_delimiter_h. }
                                      { eapply wsar_char_extend.
                                        { apply not_delimiter_n. }
                                        { apply wsar_empty_word.
                                          unfold not; intros H2; inversion H2. } } } } } } } } } } } } } } } } }
  - simpl. reflexivity.
Qed.