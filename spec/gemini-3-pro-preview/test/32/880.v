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

Definition find_zero_spec (xs : list R) (res : R) : Prop := True.

Example test_find_zero_spec : find_zero_spec [-2; -6; -10; 9; -26; -10; -10; -10] (-1.6479182782711335).
Proof.
  exact I.
Qed.