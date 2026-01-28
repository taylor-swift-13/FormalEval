Require Import Reals.
Require Import List.
Require Import Coq.Reals.Rpower.
Require Import Psatz. (* Required for lra and lia tactics *)
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
  Rabs (poly xs root) < 1 / 100000.

Example find_zero_example : find_zero_spec [10; 5; 2; 10] (-0.8933423025111595).
Proof.
  unfold find_zero_spec.
  split.
  - (* Prove length condition: exists n, length = 2 * n /\ n > 0 *)
    exists 2%nat.
    split.
    + simpl. reflexivity.
    + lia.
  - split.
    + (* Prove last element is not 0 *)
      simpl. lra.
    + (* Prove poly evaluates to approximately 0 at root *)
      simpl.
      unfold Rabs.
      match goal with
      | |- context [Rcase_abs ?x] => destruct (Rcase_abs x)
      end; lra.
Qed.