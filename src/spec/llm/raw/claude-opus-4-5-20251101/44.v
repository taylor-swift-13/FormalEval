
Require Import Coq.ZArith.ZArith.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.

Open Scope Z_scope.
Open Scope string_scope.

Fixpoint digit_to_char (d : Z) : string :=
  match d with
  | 0 => "0"
  | 1 => "1"
  | 2 => "2"
  | 3 => "3"
  | 4 => "4"
  | 5 => "5"
  | 6 => "6"
  | 7 => "7"
  | 8 => "8"
  | 9 => "9"
  | _ => ""
  end.

Fixpoint base_repr_aux (x : Z) (base : Z) (fuel : nat) (acc : string) : string :=
  match fuel with
  | O => acc
  | S fuel' =>
    if x =? 0 then acc
    else base_repr_aux (x / base) base fuel' (append (digit_to_char (x mod base)) acc)
  end.

Definition change_base_spec (x : Z) (base : Z) (result : string) : Prop :=
  (2 <= base < 10) /\
  (x >= 0) /\
  ((x = 0 /\ result = "0") \/
   (x > 0 /\ exists fuel : nat, result = base_repr_aux x base fuel "")).
