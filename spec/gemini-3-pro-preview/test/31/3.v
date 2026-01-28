Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Znumtheory.
Require Import Coq.micromega.Lia.
Open Scope Z_scope.

Definition is_prime_spec (n : Z) (result : bool) : Prop :=
  result = true <-> prime n.

Example test_is_prime_11 : is_prime_spec 11 true.
Proof.
  unfold is_prime_spec.
  split.
  - (* Case: true = true -> prime 11 *)
    intros _.
    split.
    + (* 1 < 11 *)
      lia.
    + (* forall n, 1 <= n < 11 -> rel_prime n 11 *)
      intros n Hn.
      (* We verify gcd(n, 11) = 1 for all n in range *)
      assert (Hcases: n = 1 \/ n = 2 \/ n = 3 \/ n = 4 \/ n = 5 \/ 
                      n = 6 \/ n = 7 \/ n = 8 \/ n = 9 \/ n = 10) by lia.
      destruct Hcases as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]];
      apply Zgcd_1_rel_prime; compute; reflexivity.
  - (* Case: prime 11 -> true = true *)
    intros _.
    reflexivity.
Qed.