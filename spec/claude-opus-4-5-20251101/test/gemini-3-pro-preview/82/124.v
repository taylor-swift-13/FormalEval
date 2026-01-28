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

Example test_prime_length_long : prime_length_spec "ThequickbrownfoxjumpsoverthelazydogThequickbrownfoxjumpsoverthelazydogThequickbrownfoxjumpsoverthelazydogThequickbrownfoxjumpsoverthelazydogThequickbrownfoxjumpsoverthelazydog" false.
Proof.
  unfold prime_length_spec.
  simpl.
  split.
  - intro H. discriminate H.
  - intro Hprime.
    unfold is_prime in Hprime.
    destruct Hprime as [_ Hforall].
    specialize (Hforall 5).
    assert (H2: 2 <= 5) by lia.
    assert (Hsq: 5 * 5 <= 175) by lia.
    specialize (Hforall H2 Hsq).
    exfalso.
    apply Hforall.
    reflexivity.
Qed.