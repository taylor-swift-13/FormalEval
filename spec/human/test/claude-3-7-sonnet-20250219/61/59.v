Require Import Coq.Lists.List Coq.Strings.Ascii Coq.Strings.String.
Import ListNotations.
Open Scope string_scope.

Fixpoint correct_bracketing_aux (s : string) (depth : nat) : bool :=
  match s with
  | "" => match depth with 0 => true | _ => false end
  | String c s' =>
    if (Ascii.eqb c "(")%char then
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

Example test_case_1 : problem_61_spec "()(((())))))" false.
Proof.
  unfold problem_61_spec, correct_bracketing.
  simpl.
  (* Evaluate correct_bracketing_aux "()(((())))))" 0 step-by-step *)
  (* String "(" (String ")" (String "(" (String "(" (String "(" (String "(" (String ")" (String ")" (String ")" (String ")" (String ")" "")))))))))) *)
  (* Step 1: Ascii.eqb '(' '(' = true -> depth 0 -> 1 *)
  (* Step 2: Ascii.eqb ')' '(' = false, Ascii.eqb ')' ')' = true -> depth 1 -> 0 *)
  (* Step 3: Ascii.eqb '(' '(' = true -> depth 0 -> 1 *)
  (* Step 4: Ascii.eqb '(' '(' = true -> depth 1 -> 2 *)
  (* Step 5: Ascii.eqb '(' '(' = true -> depth 2 -> 3 *)
  (* Step 6: Ascii.eqb '(' '(' = true -> depth 3 -> 4 *)
  (* Step 7: Ascii.eqb ')' '(' = false, Ascii.eqb ')' ')' = true -> depth 4 -> 3 *)
  (* Step 8: Ascii.eqb ')' '(' = false, Ascii.eqb ')' ')' = true -> depth 3 -> 2 *)
  (* Step 9: Ascii.eqb ')' '(' = false, Ascii.eqb ')' ')' = true -> depth 2 -> 1 *)
  (* Step 10: Ascii.eqb ')' '(' = false, Ascii.eqb ')' ')' = true -> depth 1 -> 0 *)
  (* Step 11: Ascii.eqb ')' '(' = false, Ascii.eqb ')' ')' = true -> depth 0 -> false (because closing when depth=0 is false) *)
  reflexivity.
Qed.