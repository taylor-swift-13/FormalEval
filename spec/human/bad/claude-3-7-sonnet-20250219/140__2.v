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
       | c' :: _ => c' <> space
       end) ->
      fix_spaces_relation i' o' ->
      fix_spaces_relation (space :: i') (underscore :: o')
  | fsr_multi_space (i_after_2_spaces i_rem o' : list ascii):
      skip_leading_spaces i_after_2_spaces i_rem ->
      fix_spaces_relation i_rem o' ->
      fix_spaces_relation (space :: space :: i_after_2_spaces) (dash :: o').

Definition problem_140_spec (s_in s_out : string) : Prop :=
  fix_spaces_relation (list_ascii_of_string s_in) (list_ascii_of_string s_out).

Example fix_spaces_example :
  problem_140_spec "Mudasir Hanif " "Mudasir_Hanif_".
Proof.
  unfold problem_140_spec.
  simpl.
  (* The input string "Mudasir Hanif " as list ascii:
     "M"::"u"::"d"::"a"::"s"::"i"::"r"::" "::
     "H"::"a"::"n"::"i"::"f"::" "::[]
  *)
  (* The output string "Mudasir_Hanif_" as list ascii:
     "M"::"u"::"d"::"a"::"s"::"i"::"r"::"_"::
     "H"::"a"::"n"::"i"::"f"::"_"::[]
  *)
  repeat match goal with
  | |- fix_spaces_relation [] [] =>
      apply fsr_nil
  | |- fix_spaces_relation (space :: ?i') (underscore :: ?o') =>
      apply fsr_single_space;
      [ destruct i' as [|c' i''] eqn:?; try discriminate; discriminate |]
  | |- fix_spaces_relation ( ?c :: ?i') ( ?c' :: ?o') =>
      (* Here c and c' should be the same non-space character *)
      first
        [ (* If c = c' and both not space *)
          unify c c'; 
          apply fsr_non_space; [unfold not; intro H; discriminate | idtac] 
        | fail 1 ]
  end.
Qed.