Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Lia.

Open Scope Z_scope.

Definition divides (d n : Z) : Prop :=
  exists k : Z, n = d * k.

Definition is_prime_pred (n : Z) : Prop :=
  2 <= n /\ forall i : Z, 2 <= i <= Z.sqrt n -> ~ divides i n.

Definition is_prime_spec (n : Z) (b : bool) : Prop :=
  (b = true <-> is_prime_pred n) /\ (b = false <-> ~ is_prime_pred n).

Example test_is_prime_6 : is_prime_spec 6 false.
Proof.
  unfold is_prime_spec, is_prime_pred, divides.
  split.
  - (* b = true <-> is_prime_pred 6 *)
    split.
    + (* true -> is_prime_pred 6 *)
      intro H. discriminate H.
    + (* is_prime_pred 6 -> true *)
      intro H.
      destruct H as [H1 H2].
      assert (Hsqrt: Z.sqrt 6 = 2) by reflexivity.
      assert (H2cond: 2 <= 2 <= Z.sqrt 6).
      { rewrite Hsqrt. lia. }
      specialize (H2 2 H2cond).
      exfalso.
      apply H2.
      exists 3. reflexivity.
  - (* b = false <-> ~ is_prime_pred 6 *)
    split.
    + (* false -> ~ is_prime_pred 6 *)
      intro H.
      intro Hprime.
      destruct Hprime as [H1 H2].
      assert (Hsqrt: Z.sqrt 6 = 2) by reflexivity.
      assert (H2cond: 2 <= 2 <= Z.sqrt 6).
      { rewrite Hsqrt. lia. }
      specialize (H2 2 H2cond).
      apply H2.
      exists 3. reflexivity.
    + (* ~ is_prime_pred 6 -> false *)
      intro H. reflexivity.
Qed.