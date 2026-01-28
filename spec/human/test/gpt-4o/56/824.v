Require Import Coq.Lists.List.
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Open Scope string_scope.

Fixpoint correct_bracketing_aux (s : string) (depth : nat) : bool :=
  match s with
  | "" => match depth with 0 => true | _ => false end
  | String c s' =>
    if (Ascii.eqb c "<"%char) then
      correct_bracketing_aux s' (S depth)
    else if (Ascii.eqb c ">"%char) then
      match depth with
      | 0 => false
      | S d => correct_bracketing_aux s' d
      end
    else
      correct_bracketing_aux s' depth
  end.

Definition correct_bracketing (s : string) : bool :=
  correct_bracketing_aux s 0.

Definition problem_56_pre (brackets : string) : Prop :=
  Forall (fun c => c = "<"%char \/ c = ">"%char) (list_ascii_of_string brackets).

Definition problem_56_spec (brackets : string) (b : bool) : Prop :=
  b = correct_bracketing brackets.

Example test_correct_bracketing_1 : problem_56_spec "<><<<<<<><<<<>>>><<<<<<<>>>><<>>><>>>>>>><<<<<<<<><<<<>>>><<<<<<<><>><<<><<>><<<>>>><<<<<>>>>>>><<<<<<<>><><<<<>>>><<<<<<<>>>><<>>><>>>>>><<<<<<<>>>>>>>><<<<<>><>>>>>>><<>>><><><<<<>>>>><>>>>><<<><<<<>>>>>>><<<<<<>>>>>>>>>><<<<<<<<<<<<>>>>><<<<<>>>>>>>>><<<<<<<>>>><><>>><><><<<<>>>>><>>>>><><<<<>>>>>>><<<<<<>>>>>>>>>><<<<<<<<<<<<>>>>>" false.
Proof.
  unfold problem_56_spec, correct_bracketing.
  simpl.
  reflexivity.
Qed.