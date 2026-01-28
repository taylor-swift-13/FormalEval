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

Example test_prime_length_long : prime_length_spec "ThequickbrownfoxjumpsoverthelazydogThequtheickbrownfoxjumpssoverthelazydog" false.
Proof.
  unfold prime_length_spec.
  assert (Hlen: String.length "ThequickbrownfoxjumpsoverthelazydogThequtheickbrownfoxjumpssoverthelazydog" = 74).
  { reflexivity. }
  rewrite Hlen. clear Hlen.
  split.
  - intro H. discriminate.
  - intros [Hge Hforall].
    exfalso.
    specialize (Hforall 2).
    apply Hforall.
    + lia.
    + lia.
    + reflexivity.
Qed.