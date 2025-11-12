
Require Import List.
Import ListNotations.
Require Import Nat.
Require Import Bool.

Fixpoint monotonic_inc (l : list nat) : bool :=
  match l with
  | [] => true
  | _ :: [] => true
  | x :: y :: tl => if x <=? y then monotonic_inc (y :: tl) else false
  end.

Fixpoint monotonic_dec (l : list nat) : bool :=
  match l with
  | [] => true
  | _ :: [] => true
  | x :: y :: tl => if x >=? y then monotonic_dec (y :: tl) else false
  end.

Definition monotonic_spec (l : list nat) (res : bool) : Prop :=
  res = (monotonic_inc l || monotonic_dec l) = true.
