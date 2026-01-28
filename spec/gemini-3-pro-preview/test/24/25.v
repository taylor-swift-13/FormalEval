Require Import Coq.ZArith.ZArith.
Require Import Psatz.

Open Scope Z_scope.

Definition largest_divisor_spec (n : Z) (result : Z) : Prop :=
  Z.divide result n /\
  result < n /\
  (forall k : Z, Z.divide k n -> k < n -> k <= result).

Example test_largest_divisor_236: largest_divisor_spec 236 118.
Proof.
  unfold largest_divisor_spec.
  split.
  - exists 2. reflexivity.
  - split.
    + lia.
    + intros k Hdiv Hlt.
      destruct Hdiv as [x Hx]. (* Hx: 236 = x * k *)
      
      (* Analyze the sign of k *)
      destruct (Z_le_gt_dec k 0).
      * (* Case k <= 0: k <= 118 holds trivially *)
        lia.
      * (* Case k > 0 *)
        (* Since 236 = x * k and k > 0, x must be positive *)
        assert (Hx_pos: x > 0).
        { rewrite Hx in *. nia. }
        
        (* x cannot be 1 because that would imply k = 236, contradicting k < 236 *)
        assert (Hx_ge_2: x >= 2).
        { 
          destruct (Z.eq_dec x 1).
          - subst x. lia.
          - lia. 
        }
        
        (* Since 236 = x * k and x >= 2, we have 236 >= 2 * k *)
        rewrite Hx in *.
        nia.
Qed.