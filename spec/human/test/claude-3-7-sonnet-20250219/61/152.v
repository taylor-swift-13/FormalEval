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

Example test_case_1 : problem_61_spec "()(((()(()(())())())" false.
Proof.
  unfold problem_61_spec, correct_bracketing.
  simpl.
  (* Evaluate correct_bracketing_aux step-by-step for "()(((()(()(())())())" starting at 0 *)
  (* Let s = "()(((()(()(())())())" *)
  (* 1) String "(" s' with depth 0: depth -> 1 *)
  (* 2) String ")" s' with depth 1: depth -> 0 *)
  (* 3) String "(" s' with depth 0: depth -> 1 *)
  (* 4) String "(" s' with depth 1: depth -> 2 *)
  (* 5) String "(" s' with depth 2: depth -> 3 *)
  (* 6) String "(" s' with depth 3: depth -> 4 *)
  (* 7) String ")" s' with depth 4: depth -> 3 *)
  (* 8) String "(" s' with depth 3: depth -> 4 *)
  (* 9) String "(" s' with depth 4: depth -> 5 *)
  (* 10) String ")" s' with depth 5: depth -> 4 *)
  (* 11) String "(" s' with depth 4: depth -> 5 *)
  (* 12) String ")" s' with depth 5: depth -> 4 *)
  (* 13) String ")" s' with depth 4: depth -> 3 *)
  (* 14) String "(" s' with depth 3: depth -> 4 *)
  (* 15) String ")" s' with depth 4: depth -> 3 *)
  (* 16) String ")" s' with depth 3: depth -> 2 *)
  (* 17) String ")" s' with depth 2: depth -> 1 *)
  (* End of string reached with depth = 1, so correct_bracketing_aux returns false *)
  reflexivity.
Qed.