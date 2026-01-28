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

(* Helper tactic to automate splitting *)
Ltac solve_split_step :=
  match goal with
  | [ |- split_sentences_aux_rel "" _ _ ] => apply ssar_empty
  | [ |- split_sentences_aux_rel (String "." _) _ _ ] => eapply ssar_delim; [ constructor | ]
  | [ |- split_sentences_aux_rel (String "?" _) _ _ ] => eapply ssar_delim; [ constructor | ]
  | [ |- split_sentences_aux_rel (String "!" _) _ _ ] => eapply ssar_delim; [ constructor | ]
  | [ |- split_sentences_aux_rel (String _ _) _ _ ] => 
      eapply ssar_char; [ solve_not_delim | solve_append | ]
  end.

Ltac solve_split := repeat solve_split_step.

Example test_problem_91 : problem_91_spec "I forgot my phone in the car. Oh no, now I haI have a lot of work to do today. I wish I could take a nap iI enjoy reading bo oks. They help me learn new things.nstead.ve to go back and get it." 2.
Proof.
  unfold problem_91_spec.
  eexists.
  split.
  - (* Prove splitting *)
    apply ssr_build.
    solve_split.
  - (* Prove counting *)
    (* 1: "I forgot..." (Bored) *)
    eapply cbsr_bored.
    + apply tlwr_keep; reflexivity.
    + exists " forgot my phone in the car"; apply dpr_match; [ reflexivity | apply dpr_empty ].
    + (* 2: " Oh no..." (Not bored) *)
      eapply cbsr_not_bored.
      * apply tlwr_skip; [ reflexivity | apply tlwr_keep; reflexivity ].
      * intro H; destruct H as [rest H]; inversion H; simpl in H2; discriminate.
      * (* 3: " I wish..." (Bored) *)
        eapply cbsr_bored.
        -- apply tlwr_skip; [ reflexivity | apply tlwr_keep; reflexivity ].
        -- exists " wish I could take a nap iI enjoy reading bo oks"; apply dpr_match; [ reflexivity | apply dpr_empty ].
        -- (* 4: " They help..." (Not bored) *)
           eapply cbsr_not_bored.
           ++ apply tlwr_skip; [ reflexivity | apply tlwr_keep; reflexivity ].
           ++ intro H; destruct H as [rest H]; inversion H; simpl in H2; discriminate.
           ++ (* 5: "nstead" (Not bored) *)
              eapply cbsr_not_bored.
              ** apply tlwr_keep; reflexivity.
              ** intro H; destruct H as [rest H]; inversion H; simpl in H2; discriminate.
              ** (* 6: "ve to go..." (Not bored) *)
                 eapply cbsr_not_bored.
                 --- apply tlwr_keep; reflexivity.
                 --- intro H; destruct H as [rest H]; inversion H; simpl in H2; discriminate.
                 --- (* 7: "" (Not bored) *)
                     eapply cbsr_not_bored.
                     +++ apply tlwr_none.
                     +++ intro H; destruct H as [rest H]; inversion H.
                     +++ apply cbsr_nil.
Qed.