Require Import Coq.Strings.String.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Require Import Lia.

Definition is_prime (n : nat) : Prop :=
  n >= 2 /\ forall d : nat, 2 <= d -> d * d <= n -> ~(Nat.modulo n d = 0).

Definition prime_length_spec (s : string) (result : bool) : Prop :=
  let len := String.length s in
  (result = true <-> is_prime len).

Example test_long_string : prime_length_spec "LgdoOsvabcdeaabcdeaebcddefabacdabcdefgeadefggfgbcabcdeabc" false.
Proof.
  unfold prime_length_spec.
  simpl.
  split.
  - intros H.
    discriminate.
  - intros Hprime.
    unfold is_prime in Hprime.
    destruct Hprime as [Hge Hdiv].
    exfalso.
    specialize (Hdiv 3).
    assert (H2 : 2 <= 3) by lia.
    assert (Hdd : 3 * 3 <= 58) by lia.
    specialize (Hdiv H2 Hdd).
    simpl in Hdiv.
    apply Hdiv.
    reflexivity.
Qed.