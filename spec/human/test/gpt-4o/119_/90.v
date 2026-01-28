Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope string_scope.

Fixpoint list_ascii_of_string (s : string) : list ascii :=
  match s with
  | EmptyString => []
  | String c s' => c :: list_ascii_of_string s'
  end.

Fixpoint string_of_list_ascii (l : list ascii) : string :=
  match l with
  | [] => EmptyString
  | c :: l' => String c (string_of_list_ascii l')
  end.

Fixpoint check_parens_inner (l : list ascii) (counter : nat) : bool :=
  match l with
  | [] => Nat.eqb counter 0
  | "("%char :: t => check_parens_inner t (S counter)
  | ")"%char :: t =>
    match counter with
    | 0 => false
    | S n' => check_parens_inner t n'
    end
  | _ :: t => check_parens_inner t counter
  end.

Definition is_balanced (l : list ascii) : bool :=
  check_parens_inner l 0.

Definition match_parens (inputs : list string) : string :=
  match inputs with
  | [s1; s2] =>
    let l1 := list_ascii_of_string s1 in
    let l2 := list_ascii_of_string s2 in
    if orb (is_balanced (l1 ++ l2)) (is_balanced (l2 ++ l1))
    then "Yes"
    else "No"
  | _ => "No"
  end.

Example test_case : 
  match_parens [""; "())"] = "No".
Proof.
  unfold match_parens.
  simpl.
  unfold is_balanced.
  simpl.
  reflexivity.
Qed.