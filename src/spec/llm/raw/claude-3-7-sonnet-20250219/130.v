
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.

Open Scope R_scope.
Open Scope list_scope.

Fixpoint tri_val (n : nat) : R :=
  match n with
  | 0 => 1
  | 1 => 3
  | _ =>
    if Nat.even n then
      1 + INR (n / 2)
    else
      tri_val (n - 1) + tri_val (n - 2) + 1 + INR ((n + 1) / 2)
  end.

Definition tri_spec (n : nat) (l : list R) : Prop :=
  length l = n + 1 /\
  forall i, i < n + 1 -> nth i l 0 =
    match i with
    | 0 => 1
    | 1 => 3
    | _ =>
      if Nat.even i then
        1 + INR (i / 2)
      else
        tri_val (i - 1) + tri_val (i - 2) + 1 + INR ((i + 1) / 2)
    end.
