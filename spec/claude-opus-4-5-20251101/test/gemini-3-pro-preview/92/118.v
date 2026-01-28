Require Import Reals.
Require Import ZArith.
Require Import Bool.
Require Import Psatz.
Require Import Lra.

Open Scope R_scope.

Definition any_int_spec (x y z : R) (result : bool) : Prop :=
  result = true <-> 
  ((exists i : Z, IZR i = x) /\ 
   (exists i : Z, IZR i = y) /\ 
   (exists i : Z, IZR i = z) /\ 
   (x = y + z \/ y = x + z \/ z = y + x)).

Example test_any_int : any_int_spec (1437/10) (-20) (-1237/10) false.
Proof.
  unfold any_int_spec.
  split.
  - intros H. discriminate H.
  - intros [_ [_ [_ H]]].
    lra.
Qed.