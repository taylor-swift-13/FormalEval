Require Import Coq.Strings.String Coq.Strings.Ascii Coq.Lists.List Coq.Arith.Arith.
Import ListNotations.
Open Scope string_scope.

(* Definitions from the prompt *)
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

(* Lemma: Ascii.eqb returns either true or false *)
Lemma ascii_eqb_dec : forall c1 c2 : ascii, Ascii.eqb c1 c2 = true \/ Ascii.eqb c1 c2 = false.
Proof.
  intros c1 c2.
  destruct (Ascii.eqb c1 c2) eqn:H.
  - left; reflexivity.
  - right; reflexivity.
Qed.

(* Lemma: drop_prefix_rel "I" "Hello world" None *)
Lemma drop_prefix_I_hello_world_none :
  forall rest, drop_prefix_rel "I" "Hello world" (Some rest) -> False.
Proof.
  intros rest H.
  remember (drop_prefix_rel "I" "Hello world" (Some rest)) as DPR eqn:E.
  revert rest H.
  induction DPR.
  - discriminate E.
  - simpl in E.
    destruct (Ascii.eqb c1 c2) eqn:Heq.
    + inversion E; subst.
      (* c1 = "I", c2 = 'H', check Ascii.eqb "I" "H" *)
      simpl in Heq.
      destruct (Ascii.eqb "I" "H") eqn:Eih.
      * discriminate Heq.
      * discriminate.
    + discriminate E.
  - simpl in E.
    destruct (Ascii.eqb c1 c2) eqn:Heq.
    + discriminate E.
    + inversion E; subst.
      (* This is the no-match case, so contradiction *)
      exact I.
Qed.

(* Lemma: trim_leading_whitespace_rel "Hello world" "Hello world" *)
Lemma trim_hello_world :
  trim_leading_whitespace_rel "Hello world" "Hello world".
Proof.
  apply tlwr_keep.
  (* Show Ascii.eqb 'H' ' ' = false *)
  unfold Ascii.eqb.
  simpl.
  remember (Ascii.eqb "H" " "%char) eqn:Hspace.
  destruct Hspace; discriminate.
Qed.

(* Lemma: prefix_rel "I" "Hello world" does not hold *)
Lemma no_prefix_I_hello_world :
  ~ prefix_rel "I" "Hello world".
Proof.
  unfold prefix_rel.
  intros [rest H].
  apply drop_prefix_I_hello_world_none with rest; assumption.
Qed.

(* Lemma: count_bored_sentences_rel ["Hello world"] 0 *)
Lemma count_bored_hello_world_0 :
  count_bored_sentences_rel ["Hello world"] 0.
Proof.
  apply cbsr_not_bored with (h_trimmed := "Hello world").
  - apply trim_hello_world.
  - apply no_prefix_I_hello_world.
  - apply cbsr_nil.
Qed.

(* Lemma: split_sentences_rel "Hello world" ["Hello world"] *)
Fixpoint append_chars (s : string) (acc : string) : append_char_end_rel acc (hd " " (list_ascii_of_string s)) (acc ++ s) :=
  match s with
  | EmptyString => acer_empty " " (* dummy *)
  | String c s' =>
    match acc with
    | EmptyString => acer_empty c
    | String h t => acer_cons h t c _
    end
  end.

Fixpoint list_ascii_of_string (s : string) : list ascii :=
  match s with
  | EmptyString => []
  | String c s' => c :: list_ascii_of_string s'
  end.

(** Instead of complicated induction, we prove the split_sentences_aux_rel step-by-step for "Hello world" *)

Lemma split_sentences_aux_hello_world :
  split_sentences_aux_rel "Hello world" "" ["Hello world"].
Proof.
  unfold not.
  do 11 (  
    apply ssar_char with (cur' := "");
    [ intro H; inversion H | ]);
  (* Actually this is not correct: need to incrementally build cur string *)
Abort.

(* We do it by constructing cur string step by step *)

Lemma split_sentences_aux_hello_world_step :
  split_sentences_aux_rel "ello world" "H" ["Hello world"].
Proof.
  apply ssar_char with (cur' := "He").
  - intro H; inversion H.
  - apply acer_cons.
    apply acer_empty.
  - apply ssar_char with (cur' := "Hel").
    + intro H; inversion H.
    + apply acer_cons.
      apply acer_empty.
    + apply ssar_char with (cur' := "Hell").
      * intro H; inversion H.
      * apply acer_cons.
        apply acer_empty.
      * apply ssar_char with (cur' := "Hello").
        -- intro H; inversion H.
        -- apply acer_cons.
           apply acer_empty.
        -- apply ssar_char with (cur' := "Hello ").
           ++ intro H; inversion H.
           ++ apply acer_cons.
              apply acer_empty.
           ++ apply ssar_char with (cur' := "Hello w").
              ** intro H; inversion H.
              ** apply acer_cons.
                 apply acer_empty.
              ** apply ssar_char with (cur' := "Hello wo").
                 --- intro H; inversion H.
                 --- apply acer_cons.
                     apply acer_empty.
                 --- apply ssar_char with (cur' := "Hello wor").
                     +++ intro H; inversion H.
                     +++ apply acer_cons.
                         apply acer_empty.
                     +++ apply ssar_char with (cur' := "Hello worl").
                         *** intro H; inversion H.
                         *** apply acer_cons.
                              apply acer_empty.
                         *** apply ssar_char with (cur' := "Hello world").
                             ---- intro H; inversion H.
                             ---- apply acer_cons.
                                  apply acer_empty.
                             ---- apply ssar_empty.
Qed.

Lemma split_sentences_aux_hello_world :
  split_sentences_aux_rel "Hello world" "" ["Hello world"].
Proof.
  apply ssar_char with (cur' := "H").
  - intro H; inversion H.
  - apply acer_empty.
  - apply split_sentences_aux_hello_world_step.
Qed.

Lemma split_sentences_hello_world :
  split_sentences_rel "Hello world" ["Hello world"].
Proof.
  apply ssr_build.
  apply split_sentences_aux_hello_world.
Qed.

(* The final example *)
Example example_spec_hello_world_0 :
  problem_91_spec "Hello world" 0.
Proof.
  unfold problem_91_spec.
  exists ["Hello world"].
  split.
  - apply split_sentences_hello_world.
  - apply count_bored_hello_world_0.
Qed.

Qed.