Require Import List ZArith PeanoNat.
Import ListNotations.

Fixpoint factorial (n : nat) : nat :=
  match n with
  | O => 1
  | S n' => n * factorial n'
  end.

Fixpoint sum_to_n (n : nat) : nat :=
  match n with
  | O => 0
  | S n' => n + sum_to_n n'
  end.

Definition f_spec (n : nat) (result : list nat) : Prop :=
  result = map (fun i => if Nat.even i then factorial i else sum_to_n i) (seq 1 n).

Example test_case_proof : f_spec 2 [1; 2].
Proof.
  unfold f_spec.
  simpl.
  reflexivity.
Qed.