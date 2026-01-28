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

Definition problem_140_spec (s_in s_out : string) : Prop :=
  fix_spaces_relation (list_ascii_of_string s_in) (list_ascii_of_string s_out).

Example fix_spaces_yellow :
  problem_140_spec "Yellow Yellow  Dirty  Fellow" "Yellow_Yellow__Dirty__Fellow".
Proof.
  unfold problem_140_spec.
  simpl.
  repeat match goal with
  | |- fix_spaces_relation [] [] =>
    apply fsr_nil
  | |- fix_spaces_relation (space :: space :: ?tail) (dash :: ?o') =>
    eapply fsr_multi_space;
    [ (* skip_leading_spaces *) clear; induction tail as [|c cs IH];
      [ constructor
      | destruct c eqn:Ec;
        [ (* c = space *)
          apply sls_space; assumption
        | (* c <> space *)
          apply sls_non_space; discriminate
        ]
      ]
    | apply IH
    ]
  | |- fix_spaces_relation (space :: ?i') (underscore :: ?o') =>
    apply fsr_single_space;
    [ destruct i' as [|c cs]; [ auto | discriminate ]
    | idtac
    ]
  | |- fix_spaces_relation (?c :: ?i') (?c :: ?o') =>
    apply fsr_non_space;
    [ discriminate
    | idtac
    ]
  end.
Qed.