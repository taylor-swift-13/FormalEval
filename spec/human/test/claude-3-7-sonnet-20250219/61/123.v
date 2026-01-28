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

Example test_case_1 : problem_61_spec "((((())))))))())()(()((()(()(())())()())))" false.
Proof.
  unfold problem_61_spec, correct_bracketing.
  simpl.
  (* The string starts with 10 '(' brackets, increasing depth to 10 *)
  (* Then 5 ')' brackets:
     depth goes from 10 down to 5
  *)
  (* Next character is ')' at depth 5 => depth 4 *)
  (* Then ')' at depth 4 => 3 *)
  (* Then '(' at depth 3 => 4 *)
  (* ')' at depth 4 => 3 *)
  (* '(' at depth 3 => 4 *)
  (* '(' at depth 4 => 5 *)
  (* '(' at depth 5 => 6 *)
  (* ')' at depth 6 => 5 *)
  (* '(' at depth 5 => 6 *)
  (* ')' at depth 6 => 5 *)
  (* '(' at depth 5 => 6 *)
  (* ')' at depth 6 => 5 *)
  (* ')' at depth 5 => 4 *)
  (* ')' at depth 4 => 3 *)
  (* '(' at depth 3 => 4 *)
  (* ')' at depth 4 => 3 *)
  (* '(' at depth 3 => 4 *)
  (* ')' at depth 4 => 3 *)
  (* ')' at depth 3 => 2 *)
  (* ')' at depth 2 => 1 *)
  (* ')' at depth 1 => 0 *)
  (* ')' at depth 0 => false (unmatched closing bracket) *)
  reflexivity.
Qed.