Require Import Coq.Strings.String.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Require Import Lia.

Definition is_prime (n : nat) : Prop :=
  n >= 2 /\ forall d : nat, 2 <= d -> d * d <= n -> ~(Nat.modulo n d = 0).

Definition prime_length_spec (s : string) (result : bool) : Prop :=
  let len := String.length s in
  (result = true <-> is_prime len).

Example test_long_string : prime_length_spec "LfgdoOsvabcdeaabcdeaebcddefabacdabcdefgeadefggfgbcabcdeabc" false.
Proof.
  unfold prime_length_spec.
  simpl.
  split.
  - intros H.
    discriminate.
  - intros Hprime.
    unfold is_prime in Hprime.
    destruct Hprime as [Hge2 Hdiv].
    exfalso.
    assert (H: 2 <= 2) by lia.
    assert (H0: 2 * 2 <= 58) by lia.
    specialize (Hdiv 2 H H0).
    simpl in Hdiv.
    apply Hdiv.
    reflexivity.
Qed.