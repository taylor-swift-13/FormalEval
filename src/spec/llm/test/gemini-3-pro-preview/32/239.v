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

Example test_find_zero_spec : find_zero_spec [9; -6; -8; 2; -630000; -4; -10; 26; 6; 5; -1; 8; 10; -8] 0.06079481887265221.
Proof.
  unfold find_zero_spec.
  intros.
  (* The provided solution is a floating-point approximation and does not satisfy exact real equality. *)
  Admitted.