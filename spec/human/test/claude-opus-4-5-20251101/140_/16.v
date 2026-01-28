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

Lemma T_not_space : "T"%char <> space.
Proof. unfold space. discriminate. Qed.

Lemma h_not_space : "h"%char <> space.
Proof. unfold space. discriminate. Qed.

Lemma i_not_space : "i"%char <> space.
Proof. unfold space. discriminate. Qed.

Lemma s_not_space : "s"%char <> space.
Proof. unfold space. discriminate. Qed.

Lemma a_not_space : "a"%char <> space.
Proof. unfold space. discriminate. Qed.

Lemma t_not_space : "t"%char <> space.
Proof. unfold space. discriminate. Qed.

Lemma e_not_space : "e"%char <> space.
Proof. unfold space. discriminate. Qed.

Example test_this_is_a_tesst : problem_140_spec "This is  a  tesst" "This_is-a-tesst".
Proof.
  unfold problem_140_spec.
  simpl.
  apply fsr_non_space.
  - exact T_not_space.
  - apply fsr_non_space.
    + exact h_not_space.
    + apply fsr_non_space.
      * exact i_not_space.
      * apply fsr_non_space.
        -- exact s_not_space.
        -- apply fsr_single_space.
           ++ simpl. exact i_not_space.
           ++ apply fsr_non_space.
              ** exact i_not_space.
              ** apply fsr_non_space.
                 --- exact s_not_space.
                 --- apply fsr_multi_space with (i_after_2_spaces := ["a"%char; " "%char; " "%char; "t"%char; "e"%char; "s"%char; "s"%char; "t"%char]) (i_rem := ["a"%char; " "%char; " "%char; "t"%char; "e"%char; "s"%char; "s"%char; "t"%char]).
                     +++ apply sls_non_space. exact a_not_space.
                     +++ apply fsr_non_space.
                         *** exact a_not_space.
                         *** apply fsr_multi_space with (i_after_2_spaces := ["t"%char; "e"%char; "s"%char; "s"%char; "t"%char]) (i_rem := ["t"%char; "e"%char; "s"%char; "s"%char; "t"%char]).
                             ---- apply sls_non_space. exact t_not_space.
                             ---- apply fsr_non_space.
                                  ++++ exact t_not_space.
                                  ++++ apply fsr_non_space.
                                       **** exact e_not_space.
                                       **** apply fsr_non_space.
                                            ----- exact s_not_space.
                                            ----- apply fsr_non_space.
                                                  +++++ exact s_not_space.
                                                  +++++ apply fsr_non_space.
                                                        ***** exact t_not_space.
                                                        ***** apply fsr_nil.
Qed.