
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.

Fixpoint correct_bracketing_aux (brackets : list ascii) (cnt : nat) : option nat :=
  match brackets with
  | [] => Some cnt
  | x :: xs =>
      match x with
      | "("%char => correct_bracketing_aux xs (S cnt)
      | ")"%char =>
          match cnt with
          | 0 => None
          | S cnt' => correct_bracketing_aux xs cnt'
          end
      | _ => correct_bracketing_aux xs cnt
      end
  end.

Definition correct_bracketing_spec (brackets : string) (res : bool) : Prop :=
  match correct_bracketing_aux (list_ascii_of_string brackets) 0 with
  | Some 0 => res = true
  | _ => res = false
  end.
