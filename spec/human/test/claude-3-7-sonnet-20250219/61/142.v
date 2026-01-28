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

Example test_case_1 : problem_61_spec "()(())" true.
Proof.
  unfold problem_61_spec, correct_bracketing.
  simpl.
  (* "()(())" = String "(" (String ")" (String "(" (String "(" (String ")" (String ")" "")))) *)
  (* correct_bracketing_aux "()(())" 0 =
     if Ascii.eqb "(" "(" then correct_bracketing_aux ") (())" 1 else ...
     = correct_bracketing_aux ") (())" 1
  *)
  (* correct_bracketing_aux ") (())" 1 =
     if Ascii.eqb ")" "(" then false else
     if Ascii.eqb ")" ")" then
       match 1 with
       | 0 => false
       | S d => correct_bracketing_aux " (())" d
       end else ...
     = correct_bracketing_aux " (())" 0
  *)
  (* " (())" = String "(" (String "(" (String ")" (String ")" ""))) *)
  (* correct_bracketing_aux " (())" 0 =
     if Ascii.eqb "(" "(" then correct_bracketing_aux "(()" 1 else ...
     = correct_bracketing_aux "(()" 1
  *)
  (* "(()" = String "(" (String ")" (String ")" "")) *)
  (* correct_bracketing_aux "(()" 1 =
     if Ascii.eqb "(" "(" then correct_bracketing_aux ")" 2 else ...
     = correct_bracketing_aux ")" 2
  *)
  (* correct_bracketing_aux ")" 2 =
     if Ascii.eqb ")" "(" then false else
     if Ascii.eqb ")" ")" then
       match 2 with
       | 0 => false
       | S d => correct_bracketing_aux "" d
       end else ...
     = correct_bracketing_aux "" 1
  *)
  (* correct_bracketing_aux "" 1 = false *)
  (* Actually, let's re-parse carefully without comments or confusion *)

  (* Step-by-step evaluation *)

  (* correct_bracketing_aux "()(())" 0 *)
  (* = Ascii.eqb '(' '('? yes, so correct_bracketing_aux ")(())" 1 *)
  (* correct_bracketing_aux ")(())" 1 *)
  (* first char = ')'; Ascii.eqb ')' '('? no; Ascii.eqb ')' ')' yes *)
  (* depth = 1 = S d, d=0, so correct_bracketing_aux "(())" 0 *)
  (* correct_bracketing_aux "(())" 0 *)
  (* first char '('; go to correct_bracketing_aux "())" 1 *)
  (* correct_bracketing_aux "())" 1 *)
  (* first char '('; go to correct_bracketing_aux "))" 2 *)
  (* correct_bracketing_aux "))" 2 *)
  (* first char ')'; Ascii.eqb ')' '(' no; ')' ')' yes *)
  (* depth=2=S d with d=1, so correct_bracketing_aux ")" 1 *)
  (* correct_bracketing_aux ")" 1 *)
  (* first char ')'; Ascii.eqb ')' '(' no; ')' ')' yes *)
  (* depth=1=S d with d=0, so correct_bracketing_aux "" 0 *)
  (* correct_bracketing_aux "" 0 = true *)

  reflexivity.
Qed.