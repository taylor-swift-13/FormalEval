Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.

Definition space : ascii := " ".
Definition underscore : ascii := "_".
Definition dash : ascii := "-".

Inductive skip_leading_spaces: list ascii -> list ascii -> Prop :=
  | sls_nil:
      skip_leading_spaces [] []
  | sls_non_space (c : ascii) (l : list ascii):
      c <> space ->
      skip_leading_spaces (c :: l) (c :: l)
  | sls_space (l l' : list ascii):
      skip_leading_spaces l l' ->
      skip_leading_spaces (space :: l) l'.

Inductive fix_spaces_relation : list ascii -> list ascii -> Prop :=
  | fsr_nil:
      fix_spaces_relation [] []
  | fsr_non_space (c : ascii) (i' o' : list ascii):
      c <> space ->
      fix_spaces_relation i' o' ->
      fix_spaces_relation (c :: i') (c :: o')
  | fsr_single_space (i' o' : list ascii):
      (match i' with
       | [] => True
       | c :: _ => c <> space
       end) ->
      fix_spaces_relation i' o' ->
      fix_spaces_relation (space :: i') (underscore :: o')
  | fsr_multi_space (i_after_2_spaces i_rem o' : list ascii):
      skip_leading_spaces i_after_2_spaces i_rem ->
      fix_spaces_relation i_rem o' ->
      fix_spaces_relation (space :: space :: i_after_2_spaces) (dash :: o').

Definition problem_140_pre (s : string) : Prop := True.

Definition problem_140_spec (s_in s_out : string) : Prop :=
  fix_spaces_relation (list_ascii_of_string s_in) (list_ascii_of_string s_out).

Lemma E_not_space : "E"%char <> space.
Proof.
  unfold space. discriminate.
Qed.

Lemma x_not_space : "x"%char <> space.
Proof.
  unfold space. discriminate.
Qed.

Lemma a_not_space : "a"%char <> space.
Proof.
  unfold space. discriminate.
Qed.

Lemma m_not_space : "m"%char <> space.
Proof.
  unfold space. discriminate.
Qed.

Lemma p_not_space : "p"%char <> space.
Proof.
  unfold space. discriminate.
Qed.

Lemma l_not_space : "l"%char <> space.
Proof.
  unfold space. discriminate.
Qed.

Lemma e_not_space : "e"%char <> space.
Proof.
  unfold space. discriminate.
Qed.

Lemma one_not_space : "1"%char <> space.
Proof.
  unfold space. discriminate.
Qed.

Lemma two_not_space : "2"%char <> space.
Proof.
  unfold space. discriminate.
Qed.

Example test_example : problem_140_spec "   Exa 1 2 2 mple" "-Exa_1_2_2_mple".
Proof.
  unfold problem_140_spec.
  simpl.
  apply fsr_multi_space with (i_after_2_spaces := [" "%char; "E"%char; "x"%char; "a"%char; " "%char; "1"%char; " "%char; "2"%char; " "%char; "2"%char; " "%char; "m"%char; "p"%char; "l"%char; "e"%char]) (i_rem := ["E"%char; "x"%char; "a"%char; " "%char; "1"%char; " "%char; "2"%char; " "%char; "2"%char; " "%char; "m"%char; "p"%char; "l"%char; "e"%char]).
  - apply sls_space. apply sls_non_space. exact E_not_space.
  - apply fsr_non_space.
    + exact E_not_space.
    + apply fsr_non_space.
      * exact x_not_space.
      * apply fsr_non_space.
        -- exact a_not_space.
        -- apply fsr_single_space.
           ++ simpl. exact one_not_space.
           ++ apply fsr_non_space.
              ** exact one_not_space.
              ** apply fsr_single_space.
                 --- simpl. exact two_not_space.
                 --- apply fsr_non_space.
                     +++ exact two_not_space.
                     +++ apply fsr_single_space.
                         *** simpl. exact two_not_space.
                         *** apply fsr_non_space.
                             ---- exact two_not_space.
                             ---- apply fsr_single_space.
                                  ++++ simpl. exact m_not_space.
                                  ++++ apply fsr_non_space.
                                       **** exact m_not_space.
                                       **** apply fsr_non_space.
                                            ----- exact p_not_space.
                                            ----- apply fsr_non_space.
                                                  +++++ exact l_not_space.
                                                  +++++ apply fsr_non_space.
                                                        ***** exact e_not_space.
                                                        ***** apply fsr_nil.
Qed.