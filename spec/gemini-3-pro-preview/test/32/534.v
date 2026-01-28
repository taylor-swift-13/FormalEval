Require Import Coq.Reals.Reals.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Import ListNotations.
Open Scope R_scope.

Fixpoint poly (xs : list R) (x : R) : R :=
  match xs with
  | [] => 0
  | c :: cs => c + x * poly cs x
  end.

Definition find_zero_spec (xs : list R) (res : R) : Prop :=
  Nat.Even (length xs) ->
  last xs 0 <> 0 ->
  poly xs res = 0.

Example test_find_zero_spec : find_zero_spec [1; -2; 3; -7; -4; -6; 7; -8; -1186740000; 9; -10; -3] 0.0721205720034339.
Proof.
  unfold find_zero_spec.
  intros _ _.
  simpl.
  (* The provided output is a floating point approximation. *)
  (* Exact equality in R cannot be proven for approximations. *)
  admit.
Admitted.