(* HumanEval 91 - Inductive Spec *)
Require Import Coq.Strings.String Coq.Strings.Ascii Coq.Lists.List Coq.Arith.Arith.
Import ListNotations.
Open Scope string_scope.

Inductive is_sentence_delimiter : ascii -> Prop :=
| isd_dot : is_sentence_delimiter "."%char
| isd_quest : is_sentence_delimiter "?"%char
| isd_excl : is_sentence_delimiter "!"%char.

Inductive split_sentences_rel : string -> list string -> Prop :=
| ssr_empty : split_sentences_rel "" ("" :: nil)
| ssr_delim : forall c s sents, is_sentence_delimiter c ->
   split_sentences_rel s sents ->
   split_sentences_rel (String c s) sents
| ssr_char : forall c s sents, ~ is_sentence_delimiter c ->
   split_sentences_rel s sents ->
   split_sentences_rel (String c s) sents.

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
   prefix_rel "I " h_trimmed -> count_bored_sentences_rel t n ->
   count_bored_sentences_rel (h :: t) (S n)
| cbsr_not_bored : forall h h_trimmed t n, trim_leading_whitespace_rel h h_trimmed ->
   ~ prefix_rel "I " h_trimmed -> count_bored_sentences_rel t n ->
   count_bored_sentences_rel (h :: t) n.

Definition is_bored_spec (S : string) (output : nat) : Prop :=
  exists sents, split_sentences_rel S sents /\ count_bored_sentences_rel sents output.

