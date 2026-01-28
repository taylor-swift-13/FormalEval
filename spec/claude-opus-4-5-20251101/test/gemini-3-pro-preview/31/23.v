Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.micromega.Lia.

Open Scope Z_scope.

Definition is_prime_spec (n : Z) (result : bool) : Prop :=
  (n <= 1 -> result = false) /\
  (n > 1 -> 
    (result = true <-> 
      (forall d : Z, 2 <= d -> d < n -> Z.rem n d <> 0))).

Example test_is_prime_9000 : is_prime_spec 9000 false.
Proof.
  unfold is_prime_spec.
  split.
  - (* Case: n <= 1 *)
    intros H.
    lia.
  - (* Case: n > 1 *)
    intros _.
    split.
    + (* Direction: result = true -> forall d ... *)
      intros H.
      discriminate H.
    + (* Direction: (forall d ...) -> result = true *)
      intros H.
      (* We need to show a contradiction because 2 divides 9000, 
         so the hypothesis H (that no divisor exists) is false. *)
      specialize (H 2).
      assert (H_bounds: 2 <= 2 /\ 2 < 9000) by lia.
      destruct H_bounds as [H_le H_lt].
      specialize (H H_le H_lt).
      (* Compute Z.rem 9000 2 *)
      assert (H_rem: Z.rem 9000 2 = 0) by reflexivity.
      rewrite H_rem in H.
      (* H is now 0 <> 0, which is a contradiction *)
      contradiction.
Qed.