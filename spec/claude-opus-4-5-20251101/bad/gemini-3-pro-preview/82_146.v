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

Example test_prime_length_complex : prime_length_spec "MsYJFEtsgcehuqTkrPThe quick brown fox jumps Wxjmnzover the lazy dog.xBLWjpDfmvNaRlKOiVbnZIoaethe" false.
Proof.
  unfold prime_length_spec.
  lazy [String.length].
  split.
  - intro H. discriminate H.
  - intro Hprime.
    unfold is_prime in Hprime.
    destruct Hprime as [_ Hforall].
    specialize (Hforall 2).
    assert (2 <= 2) as Hle by lia.
    assert (2 * 2 <= 96) as Hsq by lia.
    specialize (Hforall Hle Hsq).
    apply Hforall.
    reflexivity.
Qed.