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

Example test_prime_length_new : prime_length_spec "LgdoOsvabcdeaabcdeaebcddefabacdabcdefgeadefggfgbcabcdeabc" false.
Proof.
  unfold prime_length_spec.
  simpl.
  split.
  - intro H. discriminate H.
  - unfold is_prime.
    intros [_ Hforall].
    exfalso.
    specialize (Hforall 3).
    assert (2 <= 3) as Hle by lia.
    assert (3 * 3 <= 57) as Hsq by lia.
    specialize (Hforall Hle Hsq).
    apply Hforall.
    reflexivity.
Qed.