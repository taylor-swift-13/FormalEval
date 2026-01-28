Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Znumtheory.
Require Import Lia.

Open Scope Z_scope.

Definition largest_divisor_spec (n res : Z) : Prop :=
  Z.divide res n /\
  ((n <= 1 /\ res = 1) \/
   (n >= 2 /\ 1 <= res < n /\
    (forall m : Z, 1 <= m < n -> Z.divide m n -> m <= res))).

Example test_case_1 : largest_divisor_spec 4 2.
Proof.
  unfold largest_divisor_spec.
  split.
  - exists 2. reflexivity.
  - right.
    split.
    + lia.
    + split.
      * lia.
      * intros m H_range H_div.
        assert (m = 1 \/ m = 2 \/ m = 3) as H_cases by lia.
        destruct H_cases as [H1 | [H2 | H3]].
        -- subst. lia.
        -- subst. lia.
        -- subst.
           apply Z.mod_divide in H_div; [| lia].
           vm_compute in H_div.
           discriminate H_div.
Qed.