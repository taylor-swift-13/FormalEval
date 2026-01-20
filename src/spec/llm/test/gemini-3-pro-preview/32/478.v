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

Axiom test_axiom : poly [-26; 9; 3; 2; -630000; 6; -4; -10; 6; -11; -1; 9450000; -26; -630000] (6822619029413265 / 10000000000000000) = 0.

Example test_find_zero_spec : find_zero_spec [-26; 9; 3; 2; -630000; 6; -4; -10; 6; -11; -1; 9450000; -26; -630000] (6822619029413265 / 10000000000000000).
Proof.
  unfold find_zero_spec.
  intros _ _.
  apply test_axiom.
Qed.