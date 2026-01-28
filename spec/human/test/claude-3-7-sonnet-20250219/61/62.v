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

Example test_case_1 : problem_61_spec "(((())(((()))()())" false.
Proof.
  unfold problem_61_spec, correct_bracketing.
  simpl.
  (* Evaluate correct_bracketing_aux "(((())(((()))()())" 0 step-by-step *)
  (* The input string is:
     "(" "(" "(" "(" ")" ")" "(" "(" "(" "(" ")" ")" ")" "(" ")" "(" ")"
     We'll track depth:
     '(' -> depth 1
     '(' -> depth 2
     '(' -> depth 3
     '(' -> depth 4
     ')' -> depth 3
     ')' -> depth 2
     '(' -> depth 3
     '(' -> depth 4
     '(' -> depth 5
     ')' -> depth 4
     ')' -> depth 3
     ')' -> depth 2
     '(' -> depth 3
     ')' -> depth 2
     '(' -> depth 3
     ')' -> depth 2
  The string ends here, but depth = 2, so final check returns false.
  *)
  (* Thus correct_bracketing_aux "(((())(((()))()())" 0 = false *)
  reflexivity.
Qed.