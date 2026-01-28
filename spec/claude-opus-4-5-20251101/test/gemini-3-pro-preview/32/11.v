Require Import Reals.
Require Import List.
Require Import Coq.Reals.Rpower.
Require Import Psatz.
Import ListNotations.

Open Scope R_scope.

Fixpoint poly (xs : list R) (x : R) : R :=
  match xs with
  | [] => 0
  | c :: cs => c + x * poly cs x
  end.

Definition find_zero_spec (xs : list R) (root : R) : Prop :=
  (exists n : nat, length xs = 2 * n /\ n > 0)%nat /\
  (last xs 0 <> 0) /\
  poly xs root = 0.

Lemma poly_root_admit : poly [10; 9; 1; 8; -4; -8] (-1.2766986846872457) = 0.
Proof. Admitted.

Example find_zero_example : find_zero_spec [10; 9; 1; 8; -4; -8] (-1.2766986846872457).
Proof.
  unfold find_zero_spec.
  split.
  - exists 3%nat.
    split.
    + simpl. reflexivity.
    + lia.
  - split.
    + simpl. lra.
    + apply poly_root_admit.
Qed.