Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
Import ListNotations.

Open Scope string_scope.
Open Scope char_scope.

(* Auxiliary function *)
Fixpoint check_parens_inner (l : list ascii) (counter : nat) : bool :=
  match l with
  | [] => Nat.eqb counter 0
  | "(" :: t => check_parens_inner t (S counter)
  | ")" :: t =>
    match counter with
    | 0 => false
    | S n' => check_parens_inner t n'
    end
  | _ :: t => check_parens_inner t counter
  end.

Definition is_balanced (l : list ascii) : bool :=
  check_parens_inner l 0.

Definition match_parens_impl (inputs : list (list ascii)) : string :=
  match inputs with
  | [s1; s2] =>
    if orb (is_balanced (s1 ++ s2)) (is_balanced (s2 ++ s1))
    then "Yes"
    else "No"
  | _ => "No"
  end.

Definition match_parens (inputs : list string) : string :=
  match_parens_impl (map list_ascii_of_string inputs).

Example test_match_parens_yes :
  match_parens ["()("; ")"] = "Yes".
Proof.
  unfold match_parens.
  unfold match_parens_impl.
  simpl.

  (* s1 = "()(" -> ["("; ")"; "("] *)
  (* s2 = ")"   -> [")"] *)

  (* Check is_balanced (s1 ++ s2) = is_balanced ["("; ")"; "("; ")"] *)

  unfold is_balanced, check_parens_inner; simpl.

  (* Step by step *)
  (* check_parens_inner ["("; ")"; "("; ")"] 0 *)
  (* = check_parens_inner [")"; "("; ")"] 1 *)
  simpl.
  (* check_parens_inner [")"; "("; ")"] 1 *)
  (* counter = 1, next char = ')' *)
  (* counter decreases: check_parens_inner ["("; ")"] 0 *)
  simpl.
  (* check_parens_inner ["("; ")"] 0 *)
  (* counter = 0, next char = '(' *)
  (* counter increases: check_parens_inner [")"] 1 *)
  simpl.
  (* check_parens_inner [")"] 1 *)
  (* counter = 1, next char = ')' *)
  (* counter decreases: check_parens_inner [] 0 *)
  simpl.
  (* check_parens_inner [] 0 = true *)

  reflexivity.
Qed.