Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Bool.Bool.
Import ListNotations.

Fixpoint string_to_list (s : string) : list ascii :=
  match s with
  | EmptyString => []
  | String c s' => c :: string_to_list s'
  end.

Fixpoint check_parens_inner (l : list ascii) (counter : nat) : bool :=
  match l with
  | [] => Nat.eqb counter 0
  | x :: t =>
    if ascii_dec x "("%char then
      check_parens_inner t (S counter)
    else if ascii_dec x ")"%char then
      match counter with
      | 0 => false
      | S n' => check_parens_inner t n'
      end
    else
      check_parens_inner t counter
  end.

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
  match_parens_impl (map string_to_list inputs).

Example test_case_correct:
  match_parens ["()("; ")"] = "Yes"%string.
Proof.
  unfold match_parens.
  simpl.
  unfold match_parens_impl.
  unfold is_balanced.
  simpl.
  reflexivity.
Qed.