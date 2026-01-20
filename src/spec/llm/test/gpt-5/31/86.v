Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.

Open Scope Z_scope.

Definition divides (d n : Z) : Prop :=
  exists k : Z, n = d * k.

Definition is_prime_pred (n : Z) : Prop :=
  2 <= n /\ forall i : Z, 2 <= i <= Z.sqrt n -> ~ divides i n.

Definition is_prime_spec (n : Z) (b : bool) : Prop :=
  (b = true <-> is_prime_pred n) /\ (b = false <-> ~ is_prime_pred n).

Lemma is_prime_13 : is_prime_pred 13.
Proof.
  unfold is_prime_pred.
  split.
  lia.
  intros i Hrange.
  destruct Hrange as [Hlow Hhigh].
  assert (Hsqrt : Z.sqrt 13 = 3) by (vm_compute; reflexivity).
  rewrite Hsqrt in Hhigh.
  destruct (Z.eq_dec i 2) as [Hi2 | Hneq2].
  subst i.
  intro Hdiv.
  unfold divides in Hdiv.
  destruct Hdiv as [k Heq].
  exfalso.
  lia.
  destruct (Z.eq_dec i 3) as [Hi3 | Hneq3].
  subst i.
  intro Hdiv.
  unfold divides in Hdiv.
  destruct Hdiv as [k Heq].
  exfalso.
  lia.
  intro Hdiv.
  exfalso.
  assert (2 < i) by lia.
  assert (i < 3) by lia.
  lia.
Qed.

Example is_prime_spec_test_13 :
  is_prime_spec 13 true.
Proof.
  unfold is_prime_spec.
  split.
  split; intro H.
  apply is_prime_13.
  reflexivity.
  split; intro H.
  intro Hprime. discriminate H.
  exfalso. apply H. apply is_prime_13.
Qed.