Require Import Coq.Strings.String.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Require Import Coq.micromega.Lia.

Open Scope string_scope.

Definition is_prime (n : nat) : Prop :=
  n >= 2 /\ forall d : nat, 2 <= d -> d * d <= n -> ~(Nat.modulo n d = 0).

Definition prime_length_spec (s : string) (result : bool) : Prop :=
  let len := String.length s in
  (result = true <-> is_prime len).

Example test_prime_length_custom : prime_length_spec "jumpsThe quick brown fox jumps Wxjmnzover the lazy dog." false.
Proof.
  unfold prime_length_spec.
  simpl.
  split.
  - intro H. discriminate H.
  - intro Hprime.
    exfalso.
    unfold is_prime in Hprime.
    destruct Hprime as [_ Hforall].
    specialize (Hforall 5).
    apply Hforall.
    + lia.
    + lia.
    + reflexivity.
Qed.