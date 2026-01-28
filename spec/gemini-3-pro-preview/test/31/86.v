Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Znumtheory.
Require Import Coq.micromega.Lia.
Open Scope Z_scope.

Definition is_prime_spec (n : Z) (result : bool) : Prop :=
  result = true <-> prime n.

Example test_is_prime_13 : is_prime_spec 13 true.
Proof.
  unfold is_prime_spec.
  split.
  - intros _.
    apply prime_intro.
    + lia.
    + intros n Hn.
      rewrite <- Zgcd_1_rel_prime.
      assert (H_cases: n = 1 \/ n = 2 \/ n = 3 \/ n = 4 \/ n = 5 \/ n = 6 \/ 
                       n = 7 \/ n = 8 \/ n = 9 \/ n = 10 \/ n = 11 \/ n = 12) by lia.
      repeat (destruct H_cases as [-> | H_cases]; [ vm_compute; reflexivity | ]).
      subst. vm_compute. reflexivity.
  - intros _. reflexivity.
Qed.