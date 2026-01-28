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

Example test_case_1 : problem_61_spec "(((()))()()(())))" false.
Proof.
  unfold problem_61_spec, correct_bracketing.
  simpl.
  (* Step 1: analyze first character "(", increase depth to 1 *)
  (* correct_bracketing_aux "(((()))()()(())))" 0 =
     correct_bracketing_aux "((()))()()(())))" 1
  *)
  (* Step 2: next "(" increment depth to 2 *)
  (* correct_bracketing_aux "((()))()()(())))" 1 =
     correct_bracketing_aux "(()))()()(())))" 2
  *)
  (* Step 3: next "(" increment depth to 3 *)
  (* correct_bracketing_aux "(()))()()(())))" 2 =
     correct_bracketing_aux "))()()(())))" 3
  *)
  (* Step 4: next "(" increment depth to 4 *)
  (* correct_bracketing_aux "))()()(())))" 3 =
     correct_bracketing_aux "))()(())))" 4
  *)
  (* Step 5: next ")" decrement depth to 3 *)
  (* correct_bracketing_aux "))()(())))" 4 =
     correct_bracketing_aux ")()(())))" 3
  *)
  (* Step 6: next ")" decrement depth to 2 *)
  (* correct_bracketing_aux ")()(())))" 3 =
     correct_bracketing_aux "()(())))" 2
  *)
  (* Step 7: next ")" decrement depth to 1 *)
  (* correct_bracketing_aux "()(())))" 2 =
     correct_bracketing_aux "(())))" 1
  *)
  (* Step 8: next "(" increment depth to 2 *)
  (* correct_bracketing_aux "(())))" 1 =
     correct_bracketing_aux ")))))" 2
  *)
  (* Step 9: next ")" decrement depth to 1 *)
  (* correct_bracketing_aux ")))))" 2 =
     correct_bracketing_aux "))))" 1
  *)
  (* Step 10: next "(" increment depth to 2 *)
  (* correct_bracketing_aux "))))" 1 =
     correct_bracketing_aux ")))" 2
  *)
  (* Step 11: next ")" decrement depth to 1 *)
  (* correct_bracketing_aux ")))" 2 =
     correct_bracketing_aux "))" 1
  *)
  (* Step 12: next "(" increment depth to 2 *)
  (* correct_bracketing_aux "))" 1 =
     correct_bracketing_aux ")" 2
  *)
  (* Step 13: next "(" increment depth to 3 *)
  (* correct_bracketing_aux ")" 2 =
     correct_bracketing_aux "" 3
  *)
  (* Step 14: next ")" decrement depth to 2 *)
  (* correct_bracketing_aux "" 3 =
     match 3 with
     | 0 => true
     | _ => false
     end = false
  *)
  reflexivity.
Qed.