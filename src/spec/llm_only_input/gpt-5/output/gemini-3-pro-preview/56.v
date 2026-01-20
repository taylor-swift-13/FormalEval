Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Bool.Bool.

Open Scope string_scope.

(* Specification definition: check that each string in the input list has balanced angle brackets ('<' and '>') *)
Definition is_lt (a : ascii) : bool :=
  Nat.eqb (nat_of_ascii a) 60.

Definition is_gt (a : ascii) : bool :=
  Nat.eqb (nat_of_ascii a) 62.

Fixpoint balanced_aux (s : string) (n : nat) : option nat :=
  match s with
  | EmptyString => Some n
  | String a s' =>
      if is_lt a then balanced_aux s' (S n)
      else if is_gt a then
             match n with
             | 0 => None
             | S n' => balanced_aux s' n'
             end
           else None
  end.

Definition balanced (s : string) : bool :=
  match balanced_aux s 0 with
  | Some 0 => true
  | _ => false
  end.

Definition check (input : list string) : bool :=
  forallb balanced input.

(* Test case: input = ["<>"], output = true *)
Example test_case : check ["<>"] = true.
Proof.
  unfold check.
  simpl.
  unfold balanced.
  simpl.
  reflexivity.
Qed.