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

Lemma M_not_space : "M"%char <> space.
Proof.
  unfold space. discriminate.
Qed.

Lemma u_not_space : "u"%char <> space.
Proof.
  unfold space. discriminate.
Qed.

Lemma d_not_space : "d"%char <> space.
Proof.
  unfold space. discriminate.
Qed.

Lemma a_not_space : "a"%char <> space.
Proof.
  unfold space. discriminate.
Qed.

Lemma s_not_space : "s"%char <> space.
Proof.
  unfold space. discriminate.
Qed.

Lemma i_not_space : "i"%char <> space.
Proof.
  unfold space. discriminate.
Qed.

Lemma r_not_space : "r"%char <> space.
Proof.
  unfold space. discriminate.
Qed.

Lemma H_not_space : "H"%char <> space.
Proof.
  unfold space. discriminate.
Qed.

Lemma n_not_space : "n"%char <> space.
Proof.
  unfold space. discriminate.
Qed.

Lemma f_not_space : "f"%char <> space.
Proof.
  unfold space. discriminate.
Qed.

Example test_mudasir_hanif : problem_140_spec "Mudasir Hanif " "Mudasir_Hanif_".
Proof.
  unfold problem_140_spec.
  simpl.
  apply fsr_non_space.
  - exact M_not_space.
  - apply fsr_non_space.
    + exact u_not_space.
    + apply fsr_non_space.
      * exact d_not_space.
      * apply fsr_non_space.
        -- exact a_not_space.
        -- apply fsr_non_space.
           ++ exact s_not_space.
           ++ apply fsr_non_space.
              ** exact i_not_space.
              ** apply fsr_non_space.
                 --- exact r_not_space.
                 --- apply fsr_single_space.
                     +++ exact H_not_space.
                     +++ apply fsr_non_space.
                         *** exact H_not_space.
                         *** apply fsr_non_space.
                             ---- exact a_not_space.
                             ---- apply fsr_non_space.
                                  ++++ exact n_not_space.
                                  ++++ apply fsr_non_space.
                                       **** exact i_not_space.
                                       **** apply fsr_non_space.
                                            ----- exact f_not_space.
                                            ----- apply fsr_single_space.
                                                  +++++ exact I.
                                                  +++++ apply fsr_nil.
Qed.