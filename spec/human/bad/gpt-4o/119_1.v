(* Import required libraries *)
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
Import ListNotations.

(* Auxiliary function check_parens_inner *)
Fixpoint check_parens_inner (l : list ascii) (counter : nat) : bool :=
  match l with
  | [] => Nat.eqb counter 0
  | "(" % char :: t => check_parens_inner t (S counter)
  | ")" % char :: t =>
    match counter with
    | 0 => false
    | S n' => check_parens_inner t n'
    end
  | _ :: t => check_parens_inner t counter
  end.

(* is_balanced function *)
Definition is_balanced (l : list ascii) : bool :=
  check_parens_inner l 0.

Definition match_parens_impl (inputs : list (list ascii)) : string :=
  match inputs with
  | [s1; s2] =>
    if orb (is_balanced (s1 ++ s2)) (is_balanced (s2 ++ s1))
    then "Yes"%string
    else "No"%string
  | _ => "No"%string
  end.

Definition match_parens (inputs : list string) : string :=
  match_parens_impl (map list_ascii_of_string inputs).

(* Precondition: inputs are of length 2 and contain only '(' or ')' *)
Definition problem_119_pre (inputs : list string) : Prop :=
  length inputs = 2 /\ Forall (fun s =>
    let l := list_ascii_of_string s in
    Forall (fun c => c = "("%char \/ c = ")"%char) l) inputs.

(* Specification: output matches the implementation *)
Definition problem_119_spec (inputs : list string) (output : string) : Prop :=
  output = match_parens inputs.

(* Test case *)
Example match_parens_example :
  problem_119_spec ["()("; ")"] "Yes".
Proof.
  unfold problem_119_spec, match_parens.
  simpl.
  unfold match_parens_impl.
  simpl.
  unfold is_balanced.
  simpl.
  
  (* Check both concatenations *)
  assert (is_balanced (list_ascii_of_string "()(" ++ list_ascii_of_string ")") = true).
  {
    unfold check_parens_inner.
    simpl.
    (* Balanced after first concatenation *)
    reflexivity.
  }
  assert (is_balanced (list_ascii_of_string ")" ++ list_ascii_of_string "()(") = false).
  {
    unfold check_parens_inner.
    simpl.
    (* Not balanced after second concatenation *)
    reflexivity.
  }
  rewrite H, H0.
  reflexivity.
Qed.