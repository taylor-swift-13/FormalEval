Require Import Coq.Lists.List Coq.Strings.Ascii Coq.Strings.String.
Import ListNotations.
Open Scope string_scope.

Fixpoint correct_bracketing_aux (s : string) (depth : nat) : bool :=
  match s with
  | "" => match depth with 0 => true | _ => false end
  | String c s' =>
    if (Ascii.eqb c "("%char) then
      correct_bracketing_aux s' (S depth)
    else if (Ascii.eqb c ")"%char) then
      match depth with
      | 0 => false
      | S d => correct_bracketing_aux s' d
      end
    else
      correct_bracketing_aux s' depth
  end.

Definition correct_bracketing (s : string) : bool :=
  correct_bracketing_aux s 0.

Definition problem_61_pre (brackets : string) : Prop :=
  Forall (fun c => c = "("%char \/ c = ")"%char) (list_ascii_of_string brackets).

Definition problem_61_spec (brackets : string) (output : bool) : Prop :=
  output = correct_bracketing brackets.

Example test_case_1 : problem_61_spec "())()()" false.
Proof.
  unfold problem_61_spec, correct_bracketing.
  simpl.
  (* correct_bracketing_aux "())()()" 0 *)
  (* = if Ascii.eqb "(" "(" then correct_bracketing_aux ")))()()" 1 else ... *)
  (* = correct_bracketing_aux ")))()()" 1 *)
  (* = if Ascii.eqb ")" "(" then ... else if Ascii.eqb ")" ")" then
        match 1 with
        | 0 => false
        | S d => correct_bracketing_aux "))()()" d
      end else ... *)
  (* = correct_bracketing_aux "))()()" 0 *)
  (* Now calling correct_bracketing_aux "))()()" 0 *)
  (* First char = ')', depth = 0, so match depth with 0 => false *)
  reflexivity.
Qed.