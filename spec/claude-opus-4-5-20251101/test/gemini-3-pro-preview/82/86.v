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

Example test_prime_length_dcabacdee : prime_length_spec "dcabacdee" false.
Proof.
  unfold prime_length_spec.
  simpl.
  split.
  - intro H. discriminate H.
  - intro Hprime.
    unfold is_prime in Hprime.
    destruct Hprime as [_ Hcheck].
    specialize (Hcheck 3).
    assert (Hle : 2 <= 3) by lia.
    assert (Hsq : 3 * 3 <= 9) by lia.
    specialize (Hcheck Hle Hsq).
    simpl in Hcheck.
    exfalso.
    apply Hcheck.
    reflexivity.
Qed.