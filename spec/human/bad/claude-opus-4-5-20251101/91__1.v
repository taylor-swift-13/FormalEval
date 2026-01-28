Require Import Coq.Strings.String Coq.Strings.Ascii Coq.Lists.List Coq.Arith.Arith.
Import ListNotations.
Open Scope string_scope.

Inductive is_sentence_delimiter : ascii -> Prop :=
| isd_dot : is_sentence_delimiter "."%char
| isd_quest : is_sentence_delimiter "?"%char
| isd_excl : is_sentence_delimiter "!"%char.

Inductive append_char_end_rel : string -> ascii -> string -> Prop :=
| acer_empty : forall c, append_char_end_rel "" c (String c "")
| acer_cons : forall h t c t', append_char_end_rel t c t' ->
   append_char_end_rel (String h t) c (String h t').

Inductive split_sentences_aux_rel : string -> string -> list string -> Prop :=
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
| cbsr_nil : count_bored_sentences_rel nil 0%nat
| cbsr_bored : forall h h_trimmed t n, trim_leading_whitespace_rel h h_trimmed ->
   prefix_rel "I" h_trimmed -> count_bored_sentences_rel t n ->
   count_bored_sentences_rel (h :: t) (S n)
| cbsr_not_bored : forall h h_trimmed t n, trim_leading_whitespace_rel h h_trimmed ->
   ~ prefix_rel "I" h_trimmed -> count_bored_sentences_rel t n ->
   count_bored_sentences_rel (h :: t) n.

Definition problem_91_pre (S : string) : Prop := True.

Definition problem_91_spec (S : string) (output : nat) : Prop :=
  exists sents, split_sentences_rel S sents /\ count_bored_sentences_rel sents output.

Lemma not_delim_H : ~ is_sentence_delimiter "H"%char.
Proof. intro Hdelim. inversion Hdelim. Qed.

Lemma not_delim_e : ~ is_sentence_delimiter "e"%char.
Proof. intro Hdelim. inversion Hdelim. Qed.

Lemma not_delim_l : ~ is_sentence_delimiter "l"%char.
Proof. intro Hdelim. inversion Hdelim. Qed.

Lemma not_delim_o : ~ is_sentence_delimiter "o"%char.
Proof. intro Hdelim. inversion Hdelim. Qed.

Lemma not_delim_space : ~ is_sentence_delimiter " "%char.
Proof. intro Hdelim. inversion Hdelim. Qed.

Lemma not_delim_w : ~ is_sentence_delimiter "w"%char.
Proof. intro Hdelim. inversion Hdelim. Qed.

Lemma not_delim_r : ~ is_sentence_delimiter "r"%char.
Proof. intro Hdelim. inversion Hdelim. Qed.

Lemma not_delim_d : ~ is_sentence_delimiter "d"%char.
Proof. intro Hdelim. inversion Hdelim. Qed.

Lemma not_prefix_I_Hello : ~ prefix_rel "I" "Hello world".
Proof.
  unfold prefix_rel. intro Hcontra. destruct Hcontra as [rest Hrest].
  inversion Hrest; subst.
  simpl in H. discriminate H.
Qed.

Example problem_91_test : problem_91_spec "Hello world" 0%nat.
Proof.
  unfold problem_91_spec.
  exists ["Hello world"%string].
  split.
  - apply ssr_build.
    apply ssar_char with (cur' := "H"%string).
    + exact not_delim_H.
    + apply acer_empty.
    + apply ssar_char with (cur' := "He"%string).
      * exact not_delim_e.
      * apply acer_cons. apply acer_empty.
      * apply ssar_char with (cur' := "Hel"%string).
        -- exact not_delim_l.
        -- apply acer_cons. apply acer_cons. apply acer_empty.
        -- apply ssar_char with (cur' := "Hell"%string).
           ++ exact not_delim_l.
           ++ apply acer_cons. apply acer_cons. apply acer_cons. apply acer_empty.
           ++ apply ssar_char with (cur' := "Hello"%string).
              ** exact not_delim_o.
              ** apply acer_cons. apply acer_cons. apply acer_cons. apply acer_cons. apply acer_empty.
              ** apply ssar_char with (cur' := "Hello "%string).
                 --- exact not_delim_space.
                 --- apply acer_cons. apply acer_cons. apply acer_cons. apply acer_cons. apply acer_cons. apply acer_empty.
                 --- apply ssar_char with (cur' := "Hello w"%string).
                     +++ exact not_delim_w.
                     +++ apply acer_cons. apply acer_cons. apply acer_cons. apply acer_cons. apply acer_cons. apply acer_cons. apply acer_empty.
                     +++ apply ssar_char with (cur' := "Hello wo"%string).
                         *** exact not_delim_o.
                         *** apply acer_cons. apply acer_cons. apply acer_cons. apply acer_cons. apply acer_cons. apply acer_cons. apply acer_cons. apply acer_empty.
                         *** apply ssar_char with (cur' := "Hello wor"%string).
                             ---- exact not_delim_r.
                             ---- apply acer_cons. apply acer_cons. apply acer_cons. apply acer_cons. apply acer_cons. apply acer_cons. apply acer_cons. apply acer_cons. apply acer_empty.
                             ---- apply ssar_char with (cur' := "Hello worl"%string).
                                  ++++ exact not_delim_l.
                                  ++++ apply acer_cons. apply acer_cons. apply acer_cons. apply acer_cons. apply acer_cons. apply acer_cons. apply acer_cons. apply acer_cons. apply acer_cons. apply acer_empty.
                                  ++++ apply ssar_char with (cur' := "Hello world"%string).
                                       **** exact not_delim_d.
                                       **** apply acer_cons. apply acer_cons. apply acer_cons. apply acer_cons. apply acer_cons. apply acer_cons. apply acer_cons. apply acer_cons. apply acer_cons. apply acer_cons. apply acer_empty.
                                       **** apply ssar_empty.
  - apply cbsr_not_bored with (h_trimmed := "Hello world"%string).
    + apply tlwr_keep. reflexivity.
    + exact not_prefix_I_Hello.
    + apply cbsr_nil.
Qed.