Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Znumtheory.
Require Import Lia.

Open Scope Z_scope.

Definition largest_divisor_spec (n res : Z) : Prop :=
  Z.divide res n /\
  ((n <= 1 /\ res = 1) \/
   (n >= 2 /\ 1 <= res < n /\
    (forall m : Z, 1 <= m < n -> Z.divide m n -> m <= res))).

Example test_case_1 : largest_divisor_spec 5 1.
Proof.
  unfold largest_divisor_spec.
  split.
  - (* Prove 1 divides 5 *)
    exists 5. reflexivity.
  - (* Prove constraints for n = 5 *)
    right.
    split.
    + lia. (* 5 >= 2 *)
    + split.
      * lia. (* 1 <= 1 < 5 *)
      * intros m H_range H_div.
        (* We need to show that if m is a divisor of 5 in [1, 5), then m <= 1 *)
        assert (m = 1 \/ m = 2 \/ m = 3 \/ m = 4) as H_cases by lia.
        destruct H_cases as [H1 | [H2 | [H3 | H4]]].
        -- (* Case m = 1 *)
           subst. lia.
        -- (* Case m = 2 *)
           subst.
           apply Z.mod_divide in H_div; [| lia].
           vm_compute in H_div.
           discriminate H_div.
        -- (* Case m = 3 *)
           subst.
           apply Z.mod_divide in H_div; [| lia].
           vm_compute in H_div.
           discriminate H_div.
        -- (* Case m = 4 *)
           subst.
           apply Z.mod_divide in H_div; [| lia].
           vm_compute in H_div.
           discriminate H_div.
Qed.