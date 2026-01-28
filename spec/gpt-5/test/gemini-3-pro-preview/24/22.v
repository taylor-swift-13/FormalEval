Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Znumtheory.
Require Import Lia.

Open Scope Z_scope.

Definition largest_divisor_spec (n res : Z) : Prop :=
  Z.divide res n /\
  ((n <= 1 /\ res = 1) \/
   (n >= 2 /\ 1 <= res < n /\
    (forall m : Z, 1 <= m < n -> Z.divide m n -> m <= res))).

Example test_case_1 : largest_divisor_spec 23 1.
Proof.
  unfold largest_divisor_spec.
  split.
  - (* Prove 1 divides 23 *)
    exists 23. reflexivity.
  - (* Prove constraints for n = 23 *)
    right.
    split.
    + lia. (* 23 >= 2 *)
    + split.
      * lia. (* 1 <= 1 < 23 *)
      * intros m H_range H_div.
        (* We need to show that if m is a divisor of 23 in [1, 23), then m <= 1 *)
        assert (m = 1 \/ (2 <= m /\ m <= 22)) as H_split by lia.
        destruct H_split as [H_one | H_check].
        -- (* Case m = 1 *)
           subst. lia.
        -- (* Case 2 <= m <= 22 *)
           assert (m = 2 \/ m = 3 \/ m = 4 \/ m = 5 \/ m = 6 \/ m = 7 \/ m = 8 \/ m = 9 \/ m = 10 \/ m = 11 \/ m = 12 \/ m = 13 \/ m = 14 \/ m = 15 \/ m = 16 \/ m = 17 \/ m = 18 \/ m = 19 \/ m = 20 \/ m = 21 \/ m = 22) as H_cases by lia.
           repeat match goal with
           | [ H : _ \/ _ |- _ ] => destruct H; [ subst; apply Z.mod_divide in H_div; [|lia]; vm_compute in H_div; discriminate | ]
           end.
           (* Last case m = 22 *)
           subst. apply Z.mod_divide in H_div; [|lia]; vm_compute in H_div; discriminate.
Qed.