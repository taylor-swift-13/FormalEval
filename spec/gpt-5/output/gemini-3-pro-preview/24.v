Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Znumtheory.
Require Import Lia.

Open Scope Z_scope.

Definition largest_divisor_spec (n res : Z) : Prop :=
  Z.divide res n /\
  ((n <= 1 /\ res = 1) \/
   (n >= 2 /\ 1 <= res < n /\
    (forall m : Z, 1 <= m < n -> Z.divide m n -> m <= res))).

Example test_case_1 : largest_divisor_spec 3 1.
Proof.
  unfold largest_divisor_spec.
  split.
  - (* Prove 1 divides 3 *)
    exists 3. reflexivity.
  - (* Prove constraints for n = 3 *)
    right.
    split.
    + lia. (* 3 >= 2 *)
    + split.
      * lia. (* 1 <= 1 < 3 *)
      * intros m H_range H_div.
        (* We need to show that if m is a divisor of 3 in [1, 3), then m <= 1 *)
        assert (m = 1 \/ m = 2) as H_cases by lia.
        destruct H_cases as [H_eq1 | H_eq2].
        -- (* Case m = 1 *)
           subst. lia.
        -- (* Case m = 2 *)
           subst.
           (* Prove 2 does not divide 3 *)
           (* Z.mod_divide: forall a b : Z, b <> 0 -> a mod b = 0 <-> (b | a) *)
           apply Z.mod_divide in H_div; [| lia].
           (* Now H_div is 3 mod 2 = 0 *)
           vm_compute in H_div.
           discriminate H_div.
Qed.