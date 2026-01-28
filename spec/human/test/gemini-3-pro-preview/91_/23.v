Require Import Coq.Strings.String Coq.Strings.Ascii Coq.Lists.List Coq.Arith.Arith.
Import ListNotations.
Open Scope string_scope.

Inductive is_sentence_delimiter : ascii -> Prop :=
| isd_dot : is_sentence_delimiter "."%char
| isd_quest : is_sentence_delimiter "?"%char
| isd_excl : is_sentence_delimiter "!"%char.

(* 将字符追加到字符串末尾的关系式定义（函数式追加的命题化描述） *)
Inductive append_char_end_rel : string -> ascii -> string -> Prop :=
| acer_empty : forall c, append_char_end_rel "" c (String c "")
| acer_cons : forall h t c t', append_char_end_rel t c t' ->
   append_char_end_rel (String h t) c (String h t').

(* 辅助关系：按句子分隔符切分，携带当前累积句子 cur *)
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

(* 对外关系：从空的当前句子开始切分 *)
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

(* Helper tactic to solve non-delimiter goals *)
Ltac solve_not_delim :=
  match goal with
  | [ |- ~ is_sentence_delimiter _ ] => intro H; inversion H
  end.

(* Helper tactic to solve append_char_end_rel goals *)
Ltac solve_append :=
  repeat constructor.

(* Helper tactic to automatically solve splitting *)
Ltac solve_split :=
  apply ssr_build;
  repeat match goal with
  | [ |- split_sentences_aux_rel "" _ _ ] => apply ssar_empty
  | [ |- split_sentences_aux_rel (String _ _) _ _ ] =>
      first [
        eapply ssar_delim; [ constructor | ]
      | eapply ssar_char; [ solve_not_delim | solve_append | ]
      ]
  end.

Example test_problem_91 : problem_91_spec "The movie we saw last night was really good, but I think I would have enjoI am very happy today. I love spending time with my friiends.yed it more if I had some popicorn. Do you like popcorn?" 1.
Proof.
  unfold problem_91_spec.
  eexists.
  split.
  - (* Prove splitting *)
    solve_split.
  - (* Prove counting *)
    (* Sentence 1: "The movie..." *)
    eapply cbsr_not_bored.
    + (* Trim *) apply tlwr_keep. reflexivity.
    + (* Not prefix "I" *)
      intro H. destruct H as [rest H]. inversion H. simpl in H2. discriminate.
    + (* Sentence 2: " I love..." *)
      eapply cbsr_bored.
      * (* Trim *) apply tlwr_skip. reflexivity. apply tlwr_keep. reflexivity.
      * (* Prefix "I" *)
        eexists. simpl. constructor. reflexivity. apply dpr_empty.
      * (* Sentence 3: "yed..." *)
        eapply cbsr_not_bored.
        -- (* Trim *) apply tlwr_keep. reflexivity.
        -- (* Not prefix "I" *)
           intro H. destruct H as [rest H]. inversion H. simpl in H2. discriminate.
        -- (* Sentence 4: " Do..." *)
           eapply cbsr_not_bored.
           ++ (* Trim *) apply tlwr_skip. reflexivity. apply tlwr_keep. reflexivity.
           ++ (* Not prefix "I" *)
              intro H. destruct H as [rest H]. inversion H. simpl in H2. discriminate.
           ++ (* Sentence 5: "" (after final delimiter) *)
              eapply cbsr_not_bored.
              ** (* Trim *) apply tlwr_none.
              ** (* Not prefix "I" *)
                 intro H. destruct H as [rest H]. inversion H.
              ** (* End of list *)
                 apply cbsr_nil.
Qed.