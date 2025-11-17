(*def correct_bracketing(brackets: str):
""" brackets is a string of "(" and ")".
return True if every opening bracket has a corresponding closing bracket.

>>> correct_bracketing("(")
False
>>> correct_bracketing("()")
True
>>> correct_bracketing("(()())")
True
>>> correct_bracketing(")(()")
False
""" *)


Require Import Coq.Lists.List Coq.Strings.Ascii.
Import ListNotations.

Inductive is_correctly_bracketed : list ascii -> Prop :=
  | cb_nil : is_correctly_bracketed []
  | cb_nest : forall l, is_correctly_bracketed l -> is_correctly_bracketed ("("%char :: l ++ [")"%char])
  | cb_concat : forall l1 l2, is_correctly_bracketed l1 -> is_correctly_bracketed l2 -> is_correctly_bracketed (l1 ++ l2).

Fixpoint check_depth (l : list ascii) (d : nat) : option nat :=
  match l with
  | [] => Some d
  | "("%char :: t => check_depth t (S d)
  | ")"%char :: t => match d with 0 => None | S d' => check_depth t d' end
  | _ :: t => check_depth t d
  end.

Definition correct_bracketing_impl (brackets : list ascii) : bool :=
  match check_depth brackets 0 with Some 0 => true | _ => false end.

Definition Pre (brackets : list ascii) : Prop :=
  Forall (fun c => c = "("%char \/ c = ")"%char) brackets.

Definition correct_bracketing_spec (brackets : list ascii) (output : bool) : Prop :=
  output = correct_bracketing_impl brackets.


