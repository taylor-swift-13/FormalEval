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

Example test_prime_length_ababcdefa : prime_length_spec "ababcdefa" false.
Proof.
  unfold prime_length_spec.
  simpl.
  split.
  - intros H.
    discriminate H.
  - intros H.
    unfold is_prime in H.
    destruct H as [_ Hforall].
    specialize (Hforall 3).
    assert (2 <= 3) as Hle by lia.
    assert (3 * 3 <= 9) as Hsq by lia.
    specialize (Hforall Hle Hsq).
    simpl in Hforall.
    contradiction.
Qed.