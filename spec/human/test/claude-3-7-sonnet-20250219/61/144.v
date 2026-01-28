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

Example test_case_1 : problem_61_spec "()(())((()()(((())))())(()))()(()())" true.
Proof.
  unfold problem_61_spec, correct_bracketing.
  simpl.
  (* Because the input string is non-trivial, reduce by unfolding correct_bracketing_aux incrementally *)
  (* correct_bracketing_aux "()(())((()()(((())))())(()))()(()())" 0 expands recursively adding 1 to depth on '(' and subtracting on ')' *)
  (* No unmatched parentheses, so the final result after complete evaluation is true *)
  (* Coq's simpl tactic may not fully resolve due to complexity; reflexivity still holds because definitions match *)
  reflexivity.
Qed.