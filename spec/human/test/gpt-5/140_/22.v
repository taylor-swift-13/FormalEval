Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Lia.
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

Local Open Scope string_scope.
Local Open Scope char_scope.

Theorem example_fix_spaces_Thish_is__a__tesst :
  problem_140_spec "Thish is  a  tesst" "Thish_is-a-tesst".
Proof.
  unfold problem_140_spec.
  simpl.
  eapply fsr_non_space.
  - intros Heq; apply (f_equal nat_of_ascii) in Heq; vm_compute in Heq; discriminate.
  - eapply fsr_non_space.
    + intros Heq; apply (f_equal nat_of_ascii) in Heq; vm_compute in Heq; discriminate.
    + eapply fsr_non_space.
      * intros Heq; apply (f_equal nat_of_ascii) in Heq; vm_compute in Heq; discriminate.
      * eapply fsr_non_space.
        { intros Heq; apply (f_equal nat_of_ascii) in Heq; vm_compute in Heq; discriminate. }
        eapply fsr_non_space.
        { intros Heq; apply (f_equal nat_of_ascii) in Heq; vm_compute in Heq; discriminate. }
        eapply fsr_single_space.
        { intros Heq; apply (f_equal nat_of_ascii) in Heq; vm_compute in Heq; discriminate. }
        eapply fsr_non_space.
        { intros Heq; apply (f_equal nat_of_ascii) in Heq; vm_compute in Heq; discriminate. }
        eapply fsr_non_space.
        { intros Heq; apply (f_equal nat_of_ascii) in Heq; vm_compute in Heq; discriminate. }
        eapply fsr_multi_space.
        { apply sls_non_space.
          intros Heq; apply (f_equal nat_of_ascii) in Heq; vm_compute in Heq; discriminate. }
        eapply fsr_non_space.
        { intros Heq; apply (f_equal nat_of_ascii) in Heq; vm_compute in Heq; discriminate. }
        eapply fsr_multi_space.
        { apply sls_non_space.
          intros Heq; apply (f_equal nat_of_ascii) in Heq; vm_compute in Heq; discriminate. }
        eapply fsr_non_space.
        { intros Heq; apply (f_equal nat_of_ascii) in Heq; vm_compute in Heq; discriminate. }
        eapply fsr_non_space.
        { intros Heq; apply (f_equal nat_of_ascii) in Heq; vm_compute in Heq; discriminate. }
        eapply fsr_non_space.
        { intros Heq; apply (f_equal nat_of_ascii) in Heq; vm_compute in Heq; discriminate. }
        eapply fsr_non_space.
        { intros Heq; apply (f_equal nat_of_ascii) in Heq; vm_compute in Heq; discriminate. }
        eapply fsr_non_space.
        { intros Heq; apply (f_equal nat_of_ascii) in Heq; vm_compute in Heq; discriminate. }
        apply fsr_nil.
Qed.