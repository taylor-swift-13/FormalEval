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
  | fsr_double_space (i' o' : list ascii):
      (match i' with
       | [] => True
       | c :: _ => c <> space
       end) ->
      fix_spaces_relation i' o' ->
      fix_spaces_relation (space :: space :: i') (underscore :: underscore :: o')
  | fsr_multi_space (i_after_3_spaces i_rem o' : list ascii):
      skip_leading_spaces i_after_3_spaces i_rem ->
      fix_spaces_relation i_rem o' ->
      fix_spaces_relation (space :: space :: space :: i_after_3_spaces) (dash :: o').

Definition problem_140_pre (s : string) : Prop := True.

Definition problem_140_spec (s_in s_out : string) : Prop :=
  fix_spaces_relation (list_ascii_of_string s_in) (list_ascii_of_string s_out).

Example test_fix_spaces_case1 : problem_140_spec "  spaces  eveThis is  a This This is  a This is  a  tes test  spaceNoSpacesHtry  where  " "__spaces__eveThis_is__a_This_This_is__a_This_is__a__tes_test__spaceNoSpacesHtry__where__".
Proof.
  unfold problem_140_spec.
  simpl.
  repeat first [
    apply fsr_nil
  | apply fsr_non_space; [ intro H; inversion H | ]
  | apply fsr_double_space; [ simpl; try reflexivity; try (intro H; inversion H) | ]
  | apply fsr_single_space; [ simpl; try reflexivity; try (intro H; inversion H) | ]
  ].
Qed.