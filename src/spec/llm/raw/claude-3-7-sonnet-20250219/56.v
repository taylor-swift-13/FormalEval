
Require Import Coq.Strings.String.
Require Import Coq.Init.Nat.

Fixpoint correct_bracketing_aux (brackets : string) (cnt : nat) : option nat :=
  match brackets with
  | EmptyString => Some cnt
  | String c rest =>
    match c with
    | "<"%char => correct_bracketing_aux rest (S cnt)
    | ">"%char =>
      match cnt with
      | 0 => None
      | S cnt' => correct_bracketing_aux rest cnt'
      end
    | _ => correct_bracketing_aux rest cnt
    end
  end.

Definition correct_bracketing_spec (brackets : string) (result : bool) : Prop :=
  result = match correct_bracketing_aux brackets 0 with
           | Some 0 => true
           | _ => false
           end.
