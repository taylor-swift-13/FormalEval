Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Znumtheory.
Require Import Coq.micromega.Lia.
Open Scope Z_scope.

Definition is_prime_spec (n : Z) (result : bool) : Prop :=
  result = true <-> prime n.

Example test_is_prime_199 : is_prime_spec 199 true.
Proof.
  unfold is_prime_spec.
  split.
  - (* Case: true = true -> prime 199 *)
    intros _.
    (* We use the decidability of primality in Znumtheory.
       In modern Coq versions, prime_dec is transparent and can be computed. *)
    let p := eval vm_compute in (prime_dec 199) in
    match p with
    | left H => exact H
    | right _ => fail "199 is prime but prime_dec returned false"
    end.
  - (* Case: prime 199 -> true = true *)
    intros _.
    reflexivity.
Qed.