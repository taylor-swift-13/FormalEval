Require Import Coq.ZArith.ZArith.
Require Import Psatz.

Open Scope Z_scope.

Definition largest_divisor_spec (n : Z) (result : Z) : Prop :=
  Z.divide result n /\
  result < n /\
  (forall k : Z, Z.divide k n -> k < n -> k <= result).

Example test_largest_divisor_22: largest_divisor_spec 22 11.
Proof.
  unfold largest_divisor_spec.
  split.
  - (* Prove Z.divide 11 22 *)
    exists 2. reflexivity.
  - split.
    + (* Prove 11 < 22 *)
      lia.
    + (* Prove maximality *)
      intros k Hdiv Hlt.
      destruct Hdiv as [x Hx]. (* 22 = x * k *)
      
      (* Check if k <= 11 or k > 11 *)
      destruct (Z_le_gt_dec k 11).
      * (* Case k <= 11: Goal holds *)
        assumption.
      * (* Case k > 11: Contradiction *)
        (* Since k > 11 and 22 = x * k, we analyze x *)
        (* k > 0 and 22 > 0 implies x > 0 *)
        assert (x > 0) by nia.
        
        (* If x = 1, then k = 22, contradicting k < 22 *)
        assert (x <> 1).
        { intro. subst x. rewrite Z.mul_1_l in Hx. lia. }
        
        (* So x >= 2 *)
        assert (x >= 2) by lia.
        
        (* Then 22 = x * k >= 2 * k > 2 * 11 = 22 *)
        (* 22 > 22 is a contradiction *)
        nia.
Qed.