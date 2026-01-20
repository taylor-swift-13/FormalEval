Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.

Definition is_simple_power_spec (x : Z) (n : Z) (b : bool) : Prop :=
(b = true <-> exists k : nat, x = Z.pow n k) /\
(b = false <-> ~ exists k : nat, x = Z.pow n k).