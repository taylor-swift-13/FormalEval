Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.

Open Scope Z_scope.

Definition divides (d n : Z) : Prop :=
  exists k : Z, n = d * k.

Definition is_prime_pred (n : Z) : Prop :=
  2 <= n /\ forall i : Z, 2 <= i <= Z.sqrt n -> ~ divides i n.

Definition is_prime_spec (n : Z) (b : bool) : Prop :=
  (b = true <-> is_prime_pred n) /\ (b = false <-> ~ is_prime_pred n).

Lemma is_prime_19 : is_prime_pred 19.
Proof.
  unfold is_prime_pred.
  split; [lia|].
  intros i Hi.
  unfold not.
  intros Hdiv.
  destruct Hi as [Hi_low Hi_up].
  assert (Hsqrt : Z.sqrt 19 = 4) by (vm_compute; reflexivity).
  rewrite Hsqrt in Hi_up.
  destruct (Z_le_gt_dec i 2) as [Hi_le2 | Hi_gt2].
  - assert (i = 2) by lia. subst i.
    destruct Hdiv as [k Heq].
    lia.
  - destruct (Z_le_gt_dec i 3) as [Hi_le3 | Hi_gt3].
    + assert (i = 3) by lia. subst i.
      destruct Hdiv as [k Heq].
      lia.
    + assert (i = 4) by lia. subst i.
      destruct Hdiv as [k Heq].
      lia.
Qed.

Example is_prime_spec_test_19 :
  is_prime_spec 19 true.
Proof.
  unfold is_prime_spec.
  split.
  - split; intro H.
    + apply is_prime_19.
    + reflexivity.
  - split; intro H.
    + exfalso. discriminate H.
    + exfalso. apply H. apply is_prime_19.
Qed.