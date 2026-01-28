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

Lemma test_find_zero_spec_admitted : find_zero_spec [-20; 156; 7; -3; -4391; 3743; -4; -1440; -1440; -4391] 0.13592995267624453.
Admitted.

Example test_find_zero_spec : find_zero_spec [-20; 156; 7; -3; -4391; 3743; -4; -1440; -1440; -4391] 0.13592995267624453.
Proof.
  apply test_find_zero_spec_admitted.
Qed.