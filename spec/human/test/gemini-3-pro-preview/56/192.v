Require Import Coq.Lists.List.
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Open Scope string_scope.

(* Helper function to convert string to list of ascii, required for problem_56_pre *)
Fixpoint list_ascii_of_string (s : string) : list ascii :=
  match s with
  | EmptyString => nil
  | String c s' => cons c (list_ascii_of_string s')
  end.

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

Definition problem_56_pre (brackets : string) : Prop :=
  Forall (fun c => c = "<"%char \/ c = ">"%char) (list_ascii_of_string brackets).

Definition problem_56_spec (brackets : string) (b : bool) : Prop :=
  b = correct_bracketing brackets.

Example test_problem_56 : problem_56_spec "<<<<<<<<<<>>>>><<<<<>>>>" false.
Proof.
  (* Unfold the specification definition *)
  unfold problem_56_spec.
  
  (* Unfold the function definition *)
  unfold correct_bracketing.
  
  (* Simplify the execution of the fixpoint *)
  simpl.
  
  (* The result of the function matches the expected output *)
  reflexivity.
Qed.