Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Znumtheory.
Require Import Coq.micromega.Lia.
Open Scope Z_scope.

Definition is_prime_spec (n : Z) (result : bool) : Prop :=
  result = true <-> prime n.

Example test_is_prime_61 : is_prime_spec 61 true.
Proof.
  unfold is_prime_spec.
  split; [intros _| intros; reflexivity].
  apply prime_alt.
  split; [lia|].
  intros n [Hge2 Hlt61] [q Hmul].
  assert (Heq: n * q = 61) by (rewrite Hmul; ring).
  assert (Hbound: n <= 7 \/ q <= 7).
  { destruct (Z_le_dec n 7); [left; auto|].
    destruct (Z_le_dec q 7); [right; auto|].
    exfalso; assert (8 <= n) by lia; assert (8 <= q) by lia; nia. }
  destruct Hbound as [H|H].
  - assert (Hcases: n=2\/n=3\/n=4\/n=5\/n=6\/n=7) by lia.
    destruct Hcases as [?|[?|[?|[?|[?|?]]]]]; subst; lia.
  - assert (Hcases: q=1\/q=2\/q=3\/q=4\/q=5\/q=6\/q=7) by lia.
    destruct Hcases as [?|[?|[?|[?|[?|[?|?]]]]]]; subst; lia.
Qed.