Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Znumtheory.
Require Import Coq.micromega.Lia.
Open Scope Z_scope.

Definition is_prime_spec (n : Z) (result : bool) : Prop :=
  result = true <-> prime n.

Example test_is_prime_9001 : is_prime_spec 9001 true.
Proof.
  unfold is_prime_spec.
  split.
  - intros _.
    (* Use the decision procedure prime_dec from Znumtheory to prove primality. *)
    (* We evaluate prime_dec 9001 using vm_compute to get the proof term. *)
    let p := eval vm_compute in (prime_dec 9001) in
    match p with
    | left H => exact H
    | right _ => fail "9001 is prime, but prime_dec returned right"
    end.
  - intros _. reflexivity.
Qed.