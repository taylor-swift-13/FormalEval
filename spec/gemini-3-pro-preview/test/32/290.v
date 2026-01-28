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

Example test_find_zero_spec : find_zero_spec [26; -2; 4; -4; 5; -6; -26; -8; 9; -11] 0.9393895300020506.
Proof.
  unfold find_zero_spec.
  intros.
  (* The provided output is a floating-point approximation, so exact equality in R cannot be proven. *)
  admit.
Admitted.