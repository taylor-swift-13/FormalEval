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

Example test_case_1 : problem_91_spec "Hello world" 0.
Proof.
  unfold problem_91_spec.
  exists ["Hello world"].
  split.
  - apply ssr_build.
    apply ssar_char with (cur' := "Hello world").
    + unfold not; intros H. inversion H.
    + induction "Hello world" as [|c s IH].
      * apply acer_empty.
      * apply acer_cons. apply IH.
    + apply ssar_empty.
  - apply cbsr_not_bored with (h_trimmed := "Hello world").
    + apply tlwr_keep. reflexivity.
    + unfold prefix_rel. intros [rest H]. inversion H.
    + apply cbsr_nil.
Qed.