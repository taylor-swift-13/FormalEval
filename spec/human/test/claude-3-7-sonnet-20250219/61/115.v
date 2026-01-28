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

Example test_case_1 : problem_61_spec "(((()))())(" false.
Proof.
  unfold problem_61_spec, correct_bracketing.
  simpl.
  (* correct_bracketing_aux "(((()))())(" 0
     = correct_bracketing_aux "((()))())(" 1
     = correct_bracketing_aux "(()))())(" 2
     = correct_bracketing_aux "()))())(" 3
     = correct_bracketing_aux "))())(" 4
     = correct_bracketing_aux ")())(" 3
     = correct_bracketing_aux "())(" 2
     = correct_bracketing_aux "))(" 1
     = correct_bracketing_aux ")(" 0
     = match 0 with 0 => true | _ => false end ??? Wait, no at this step:
     Actually at some step, depth gets to 0 but next char is ")", so false.
  *)
  simpl.
  (* Step-by-step execution *)

  (* First char '(' *)
  (* correct_bracketing_aux "(((()))())(" 0
     = correct_bracketing_aux "((()))())(" 1
  *)
  (* Second char '(' *)
  (* correct_bracketing_aux "((()))())(" 1
     = correct_bracketing_aux "(()))())(" 2
  *)
  (* Third char '(' *)
  (* correct_bracketing_aux "(()))())(" 2
     = correct_bracketing_aux ("))())(") 3
  *)
  (* Fourth char '(' *)
  (* correct_bracketing_aux "))())(" 3
     = correct_bracketing_aux ")())(" 4
  *)
  (* Fifth char ')' *)
  (* correct_bracketing_aux ")())(" 4
     match depth 4 with S d => correct_bracketing_aux ... d
     depth = 4, d = 3
     correct_bracketing_aux "())(" 3
  *)
  (* Sixth char ')' *)
  (* correct_bracketing_aux "())(" 3
     depth = 3, d = 2
     correct_bracketing_aux ")(" 2
  *)
  (* Seventh char ')' *)
  (* correct_bracketing_aux ")(" 2
     depth = 2, d = 1
     correct_bracketing_aux "(" 1
  *)
  (* Eighth char '(' *)
  (* correct_bracketing_aux "(" 1
     depth = 1 + 1 = 2
     correct_bracketing_aux "" 2
  *)

  (* Now end of string with depth = 2, so false *)

  reflexivity.
Qed.