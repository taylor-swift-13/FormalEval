Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.micromega.Lia.

Open Scope Z_scope.

Definition divides (d n : Z) : Prop :=
  exists k, n = d * k.

Definition is_prime_spec (n : Z) (b : bool) : Prop :=
  b = true <-> 
    1 < n /\
    (forall d, 1 < d < n -> ~ divides d n).

Example test_is_prime_neg1 : is_prime_spec (-1) false.
Proof.
  unfold is_prime_spec.
  split.
  - (* Case: false = true -> ... *)
    intro H.
    discriminate H.
  - (* Case: ... -> false = true *)
    intro H.
    destruct H as [H_gt_1 _].
    (* 1 < -1 is false *)
    lia.
Qed.