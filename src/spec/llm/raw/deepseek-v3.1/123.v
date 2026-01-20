
Require Import List ZArith.
Import ListNotations.
Open Scope Z_scope.

Inductive collatz_step : Z -> Z -> Prop :=
| step_even : forall x, x > 0 -> x mod 2 = 0 -> collatz_step x (x / 2)
| step_odd : forall x, x > 0 -> x mod 2 = 1 -> collatz_step x (3 * x + 1).

Inductive collatz_sequence : Z -> list Z -> Prop :=
| seq_base : forall x, x = 1 -> collatz_sequence x [1]
| seq_step : forall x y seq, x > 1 -> collatz_step x y -> collatz_sequence y seq -> collatz_sequence x (x :: seq).

Definition get_odd_collatz_spec (n : Z) (result : list Z) : Prop :=
  n > 0 /\ exists seq, collatz_sequence n seq /\
  result = sort Z.le (filter (fun x => x mod 2 = 1) seq).
