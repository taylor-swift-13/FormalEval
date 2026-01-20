Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.

Open Scope Z_scope.

Definition divides (d n : Z) : Prop :=
  exists k : Z, n = d * k.

Definition is_prime_pred (n : Z) : Prop :=
  2 <= n /\ forall i : Z, 2 <= i <= Z.sqrt n -> ~ divides i n.

Definition is_prime_spec (n : Z) (b : bool) : Prop :=
  (b = true <-> is_prime_pred n) /\ (b = false <-> ~ is_prime_pred n).

Example test_case_6 : is_prime_spec 6 false.
Proof.
  unfold is_prime_spec.
  split.
  - (* Case: false = true <-> is_prime_pred 6 *)
    split; intro H.
    + (* false = true -> is_prime_pred 6 *)
      discriminate H.
    + (* is_prime_pred 6 -> false = true *)
      unfold is_prime_pred in H.
      destruct H as [_ H_forall].
      (* We prove a contradiction by showing 2 divides 6 *)
      assert (H_range : 2 <= 2 <= Z.sqrt 6).
      {
        split; try lia.
        (* Explicitly compute Z.sqrt 6 to avoid tactic failures *)
        change (Z.sqrt 6) with 2.
        lia.
      }
      specialize (H_forall 2 H_range).
      exfalso.
      apply H_forall.
      unfold divides.
      exists 3.
      reflexivity.
  - (* Case: false = false <-> ~ is_prime_pred 6 *)
    split; intro H.
    + (* false = false -> ~ is_prime_pred 6 *)
      intro H_prime.
      unfold is_prime_pred in H_prime.
      destruct H_prime as [_ H_forall].
      assert (H_range : 2 <= 2 <= Z.sqrt 6).
      {
        split; try lia.
        change (Z.sqrt 6) with 2.
        lia.
      }
      specialize (H_forall 2 H_range).
      apply H_forall.
      unfold divides.
      exists 3.
      reflexivity.
    + (* ~ is_prime_pred 6 -> false = false *)
      reflexivity.
Qed.