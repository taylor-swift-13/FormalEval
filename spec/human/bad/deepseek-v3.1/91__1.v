Require Import Coq.Strings.String Coq.Strings.Ascii Coq.Lists.List Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope string_scope.

(* Definitions from the problem statement *)

Inductive is_sentence_delimiter : ascii -> Prop :=
| isd_dot : is_sentence_delimiter "."%char
| isd_quest : is_sentence_delimiter "?"%char
| isd_excl : is_sentence_delimiter "!"%char.

Inductive append_char_end_rel : string -> ascii -> string -> Prop :=
| acer_empty : forall c, append_char_end_rel "" c (String c "")
| acer_cons : forall h t c t', append_char_end_rel t c t' ->
   append_char_end_rel (String h t) c (String h t').

Inductive split_sentences_aux_rel : string -> string (*cur*) -> list string -> Prop :=
| ssar_empty : forall cur, split_sentences_aux_rel "" cur (cur :: nil)
| ssar_delim : forall c s cur sents_tail,
   is_sentence_delimiter c ->
   split_sentences_aux_rel s "" sents_tail ->
   split_sentences_aux_rel (String c s) cur (cur :: sents_tail)
| ssar_char : forall c s cur cur' sents,
   ~ is_sentence_delimiter c ->
   append_char_end_rel cur c cur' ->
   split_sentences_aux_rel s cur' sents ->
   split_sentences_aux_rel (String c s) cur sents.

Inductive split_sentences_rel : string -> list string -> Prop :=
| ssr_build : forall s sents,
   split_sentences_aux_rel s "" sents ->
   split_sentences_rel s sents.

Inductive trim_leading_whitespace_rel : string -> string -> Prop :=
| tlwr_none : trim_leading_whitespace_rel "" ""
| tlwr_skip : forall c s s', Ascii.eqb c " "%char = true ->
   trim_leading_whitespace_rel s s' ->
   trim_leading_whitespace_rel (String c s) s'
| tlwr_keep : forall c s, Ascii.eqb c " "%char = false ->
   trim_leading_whitespace_rel (String c s) (String c s).

Inductive drop_prefix_rel : string -> string -> option string -> Prop :=
| dpr_empty : forall s, drop_prefix_rel "" s (Some s)
| dpr_match : forall c1 p' c2 s' res, Ascii.eqb c1 c2 = true ->
   drop_prefix_rel p' s' res ->
   drop_prefix_rel (String c1 p') (String c2 s') res
| dpr_no_match : forall c1 p' c2 s', Ascii.eqb c1 c2 = false ->
   drop_prefix_rel (String c1 p') (String c2 s') None.

Definition prefix_rel (p s : string) : Prop :=
  exists rest, drop_prefix_rel p s (Some rest).

Inductive count_bored_sentences_rel : list string -> nat -> Prop :=
| cbsr_nil : count_bored_sentences_rel nil 0
| cbsr_bored : forall h h_trimmed t n, trim_leading_whitespace_rel h h_trimmed ->
   prefix_rel "I" h_trimmed -> count_bored_sentences_rel t n ->
   count_bored_sentences_rel (h :: t) (S n)
| cbsr_not_bored : forall h h_trimmed t n, trim_leading_whitespace_rel h h_trimmed ->
   ~ prefix_rel "I" h_trimmed -> count_bored_sentences_rel t n ->
   count_bored_sentences_rel (h :: t) n.

Definition problem_91_pre (S : string) : Prop := True.

Definition problem_91_spec (S : string) (output : nat) : Prop :=
  exists sents, split_sentences_rel S sents /\ count_bored_sentences_rel sents output.

(* Test case: input = "Hello world", output = 0 *)
Definition test_input := "Hello world".
Definition test_expected_output := 0.

(* Lemmas needed for the proof *)
Lemma append_char_end_rel_single_char : forall c, append_char_end_rel "" c (String c "").
Proof. apply acer_empty. Qed.

Lemma append_char_end_rel_cons : forall s c s', append_char_end_rel s c s' -> 
  forall h, append_char_end_rel (String h s) c (String h s').
Proof. intros s c s' H h. apply acer_cons. apply H. Qed.

Lemma not_sentence_delimiter_H : ~ is_sentence_delimiter "H"%char.
Proof.
  intro H. inversion H.
Qed.

Lemma not_sentence_delimiter_e : ~ is_sentence_delimiter "e"%char.
Proof.
  intro H. inversion H.
Qed.

Lemma not_sentence_delimiter_l : ~ is_sentence_delimiter "l"%char.
Proof.
  intro H. inversion H.
Qed.

Lemma not_sentence_delimiter_o : ~ is_sentence_delimiter "o"%char.
Proof.
  intro H. inversion H.
Qed.

Lemma not_sentence_delimiter_space : ~ is_sentence_delimiter " "%char.
Proof.
  intro H. inversion H.
Qed.

Lemma not_sentence_delimiter_w : ~ is_sentence_delimiter "w"%char.
Proof.
  intro H. inversion H.
Qed.

Lemma not_sentence_delimiter_r : ~ is_sentence_delimiter "r"%char.
Proof.
  intro H. inversion H.
Qed.

Lemma not_sentence_delimiter_d : ~ is_sentence_delimiter "d"%char.
Proof.
  intro H. inversion H.
Qed.

Lemma split_hello_world : split_sentences_aux_rel "Hello world" "" ["Hello world"].
Proof.
  apply ssar_char with (c := "H"%char) (cur' := "H"%string).
  - apply not_sentence_delimiter_H.
  - apply append_char_end_rel_single_char.
  - apply ssar_char with (c := "e"%char) (cur' := "He"%string).
    + apply not_sentence_delimiter_e.
    + apply append_char_end_rel_cons. apply append_char_end_rel_single_char.
    + apply ssar_char with (c := "l"%char) (cur' := "Hel"%string).
      * apply not_sentence_delimiter_l.
      * apply append_char_end_rel_cons. apply append_char_end_rel_cons. apply append_char_end_rel_single_char.
      * apply ssar_char with (c := "l"%char) (cur' := "Hell"%string).
        { apply not_sentence_delimiter_l. }
        { apply append_char_end_rel_cons. apply append_char_end_rel_cons. apply append_char_end_rel_cons. apply append_char_end_rel_single_char. }
        * apply ssar_char with (c := "o"%char) (cur' := "Hello"%string).
          { apply not_sentence_delimiter_o. }
          { apply append_char_end_rel_cons. apply append_char_end_rel_cons. apply append_char_end_rel_cons. apply append_char_end_rel_cons. apply append_char_end_rel_single_char. }
          * apply ssar_char with (c := " "%char) (cur' := "Hello "%string).
            { apply not_sentence_delimiter_space. }
            { apply append_char_end_rel_cons. apply append_char_end_rel_cons. apply append_char_end_rel_cons. apply append_char_end_rel_cons. apply append_char_end_rel_cons. apply append_char_end_rel_single_char. }
            * apply ssar_char with (c := "w"%char) (cur' := "Hello w"%string).
              { apply not_sentence_delimiter_w. }
              { apply append_char_end_rel_cons. apply append_char_end_rel_cons. apply append_char_end_rel_cons. apply append_char_end_rel_cons. apply append_char_end_rel_cons. apply append_char_end_rel_cons. apply append_char_end_rel_single_char. }
              * apply ssar_char with (c := "o"%char) (cur' := "Hello wo"%string).
                { apply not_sentence_delimiter_o. }
                { apply append_char_end_rel_cons. apply append_char_end_rel_cons. apply append_char_end_rel_cons. apply append_char_end_rel_cons. apply append_char_end_rel_cons. apply append_char_end_rel_cons. apply append_char_end_rel_cons. apply append_char_end_rel_single_char. }
                * apply ssar_char with (c := "r"%char) (cur' := "Hello wor"%string).
                  { apply not_sentence_delimiter_r. }
                  { apply append_char_end_rel_cons. apply append_char_end_rel_cons. apply append_char_end_rel_cons. apply append_char_end_rel_cons. apply append_char_end_rel_cons. apply append_char_end_rel_cons. apply append_char_end_rel_cons. apply append_char_end_rel_cons. apply append_char_end_rel_single_char. }
                  * apply ssar_char with (c := "l"%char) (cur' := "Hello worl"%string).
                    { apply not_sentence_delimiter_l. }
                    { apply append_char_end_rel_cons. apply append_char_end_rel_cons. apply append_char_end_rel_cons. apply append_char_end_rel_cons. apply append_char_end_rel_cons. apply append_char_end_rel_cons. apply append_char_end_rel_cons. apply append_char_end_rel_cons. apply append_char_end_rel_cons. apply append_char_end_rel_single_char. }
                    * apply ssar_char with (c := "d"%char) (cur' := "Hello world"%string).
                      { apply not_sentence_delimiter_d. }
                      { apply append_char_end_rel_cons. apply append_char_end_rel_cons. apply append_char_end_rel_cons. apply append_char_end_rel_cons. apply append_char_end_rel_cons. apply append_char_end_rel_cons. apply append_char_end_rel_cons. apply append_char_end_rel_cons. apply append_char_end_rel_cons. apply append_char_end_rel_cons. apply append_char_end_rel_single_char. }
                      * apply ssar_empty.
Qed.

Lemma trim_leading_whitespace_hello_world : trim_leading_whitespace_rel "Hello world" "Hello world".
Proof.
  apply tlwr_keep.
  compute. reflexivity.
Qed.

Lemma not_prefix_I_hello_world : ~ prefix_rel "I" "Hello world".
Proof.
  intro H.
  destruct H as [rest Hdrop].
  inversion Hdrop.
  - discriminate.
  - compute in H0. discriminate.
Qed.

Lemma count_bored_nil : count_bored_sentences_rel [] 0.
Proof. apply cbsr_nil. Qed.

Example proof_boredness_for_hello_world :
  problem_91_spec test_input test_expected_output.
Proof.
  unfold problem_91_spec, test_input, test_expected_output.
  exists ["Hello world"].
  split.
  - apply ssr_build. apply split_hello_world.
  - apply cbsr_not_bored with (h_trimmed := "Hello world").
    + apply trim_leading_whitespace_hello_world.
    + apply not_prefix_I_hello_world.
    + apply count_bored_nil.
Qed.