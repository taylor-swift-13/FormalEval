Require Import Coq.Lists.List.
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Import ListNotations.
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

Example test_case_1 : correct_bracketing "<<<<<>>><><><>>>>>><" = false.
Proof.
  unfold correct_bracketing.
  simpl.
  reflexivity.
Qed.