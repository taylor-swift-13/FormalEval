Require Import Coq.ZArith.ZArith.
Require Import Psatz.

Open Scope Z_scope.

Definition largest_divisor_spec (n : Z) (result : Z) : Prop :=
  Z.divide result n /\
  result < n /\
  (forall k : Z, Z.divide k n -> k < n -> k <= result).

Example test_largest_divisor_3: largest_divisor_spec 3 1.
Proof.
  unfold largest_divisor_spec.
  split.
  - (* Prove Z.divide 1 3 *)
    exists 3. reflexivity.
  - split.
    + (* Prove 1 < 3 *)
      lia.
    + (* Prove maximality *)
      intros k Hdiv Hlt.
      destruct Hdiv as [x Hx]. (* Hx: 3 = x * k *)
      
      (* Perform case analysis on k *)
      assert (k <= 1 \/ k = 2 \/ k >= 3) as Hcases by lia.
      destruct Hcases as [Hle1 | [Hk2 | Hge3]].
      
      * (* Case k <= 1: The goal k <= 1 holds trivially *)
        exact Hle1.
        
      * (* Case k = 2: Show that 2 does not divide 3 *)
        subst k.
        (* If 3 = x * 2, then 3 mod 2 must be equal to (x * 2) mod 2 *)
        assert (Hmod: 3 mod 2 = (x * 2) mod 2).
        { rewrite <- Hx. reflexivity. }
        (* Simplify (x * 2) mod 2 to 0 using Z.mod_mul *)
        rewrite Z.mod_mul in Hmod; [| lia].
        (* Simplify 3 mod 2 to 1 *)
        simpl in Hmod.
        (* 1 = 0 is a contradiction *)
        discriminate.
        
      * (* Case k >= 3: Contradicts hypothesis k < 3 *)
        lia.
Qed.