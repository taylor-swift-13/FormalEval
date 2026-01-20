Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Znumtheory.
Require Import Coq.micromega.Lia.

Open Scope Z_scope.

Definition largest_divisor_spec (n res : Z) : Prop :=
  Z.divide res n /\
  ((n <= 1 /\ res = 1) \/
   (n >= 2 /\ 1 <= res < n /\
    (forall m : Z, 1 <= m < n -> Z.divide m n -> m <= res))).

Example test_largest_divisor_3 : largest_divisor_spec 3 1.
Proof.
  unfold largest_divisor_spec.
  split.
  - (* Prove Z.divide 1 3 *)
    exists 3. reflexivity.
  - (* Prove the specific conditions for n=3, res=1 *)
    right.
    split.
    + (* 3 >= 2 *)
      lia.
    + split.
      * (* 1 <= 1 < 3 *)
        lia.
      * (* For all m, if m divides 3 and 1 <= m < 3, then m <= 1 *)
        intros m H_range H_div.
        (* Since 1 <= m < 3, m can only be 1 or 2 *)
        assert (m = 1 \/ m = 2) as H_cases by lia.
        destruct H_cases as [H_m1 | H_m2].
        -- (* Case m = 1 *)
           rewrite H_m1. lia.
        -- (* Case m = 2 *)
           rewrite H_m2 in H_div.
           (* We need to show 2 does not divide 3 to derive a contradiction *)
           apply Z.mod_divide in H_div.
           ++ (* Compute 3 mod 2 and show it is not 0 *)
              vm_compute in H_div.
              discriminate.
           ++ (* Prove divisor is non-zero *)
              lia.
Qed.