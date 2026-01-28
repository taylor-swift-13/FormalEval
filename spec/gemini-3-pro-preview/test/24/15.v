Require Import Coq.ZArith.ZArith.
Require Import Psatz.

Open Scope Z_scope.

Definition largest_divisor_spec (n : Z) (result : Z) : Prop :=
  Z.divide result n /\
  result < n /\
  (forall k : Z, Z.divide k n -> k < n -> k <= result).

Example test_largest_divisor_81: largest_divisor_spec 81 27.
Proof.
  unfold largest_divisor_spec.
  split.
  - exists 3. reflexivity.
  - split.
    + lia.
    + intros k Hdiv Hlt.
      destruct Hdiv as [z Hz]. (* Hz: 81 = z * k *)
      
      assert (k <= 27 \/ k > 27) as Hcases by lia.
      destruct Hcases as [Hle | Hgt].
      
      * exact Hle.
        
      * (* Case k > 27: Derive contradiction *)
        (* Since k > 27 and k | 81, the cofactor z must be small *)
        assert (Hz_eq: z * k = 81) by (rewrite Hz; reflexivity).
        
        assert (z < 3).
        { 
          assert (z >= 3 -> False).
          { intro. nia. } (* 81 = z*k >= 3*28 = 84 > 81, contradiction *)
          lia. 
        }
        
        assert (z > 1).
        {
          assert (z <= 1 -> False).
          { intro. nia. } (* If z=1, k=81, contradicts k < 81. If z<=0, impossible. *)
          lia.
        }
        
        (* Therefore z must be 2 *)
        assert (z = 2) by lia.
        subst z.
        
        (* 81 = 2 * k implies 81 is even, which is false *)
        assert (Hmod: 81 mod 2 = (2 * k) mod 2).
        { rewrite Hz. reflexivity. }
        
        (* Use commutativity to match Z.mod_mul pattern (a * b) mod b *)
        rewrite Z.mul_comm in Hmod.
        rewrite Z.mod_mul in Hmod; [| lia].
        
        (* 1 = 0 is a contradiction *)
        discriminate Hmod.
Qed.