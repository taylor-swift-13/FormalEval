Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.Init.Nat.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.PeanoNat.

Open Scope R_scope.

Fixpoint poly_eval (xs : list R) (x : R) : R :=
  match xs with
  | nil => 0
  | a :: tl => a + x * poly_eval tl x
  end.

Fixpoint deriv_coeffs_aux (xs : list R) (k : nat) : list R :=
  match xs with
  | nil => nil
  | a :: tl => (INR k * a) :: deriv_coeffs_aux tl (S k)
  end.

Definition deriv_coeffs (xs : list R) : list R :=
  match xs with
  | nil => nil
  | _ :: tl => deriv_coeffs_aux tl 1
  end.

Definition derivative_eval (xs : list R) (x : R) : R :=
  poly_eval (deriv_coeffs xs) x.

Fixpoint iterate (xs : list R) (n : nat) : R :=
  match n with
  | 0 => 0
  | S k =>
      let xk := iterate xs k in
      xk - poly_eval xs xk / derivative_eval xs xk
  end.

Definition tol : R := (INR 1) / (INR 100000).

Fixpoint last_opt (xs : list R) : option R :=
  match xs with
  | nil => None
  | a :: nil => Some a
  | _ :: tl => last_opt tl
  end.

Definition last_nonzero (xs : list R) : Prop :=
  match last_opt xs with
  | Some a => a <> 0
  | None => False
  end.

Definition poly_spec (xs : list R) (x : R) (y : R) : Prop :=
  y = poly_eval xs x.

Definition find_zero_spec (xs : list R) (x : R) : Prop :=
  Nat.even (length xs) = true /\
  last_nonzero xs /\
  exists k : nat,
    k <= 1000 /\ x = iterate xs k /\ (k = 1000 \/ Rabs (poly_eval xs x) < tol).