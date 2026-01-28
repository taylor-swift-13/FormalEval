Require Import Coq.ZArith.ZArith.
Require Import Psatz.

Open Scope Z_scope.

Definition largest_divisor_spec (n : Z) (result : Z) : Prop :=
  Z.divide result n /\
  result < n /\
  (forall k : Z, Z.divide k n -> k < n -> k <= result).

Example test_largest_divisor_7: largest_divisor_spec 7 1.
Proof.
  unfold largest_divisor_spec.
  split.
  - (* Prove Z.divide 1 7 *)
    exists 7. reflexivity.
  - split.
    + (* Prove 1 < 7 *)
      lia.
    + (* Prove maximality *)
      intros k Hdiv Hlt.
      destruct Hdiv as [x Hx]. (* Hx: 7 = x * k *)
      
      (* Perform case analysis on k *)
      assert (k <= 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k >= 7) as Hcases by lia.
      destruct Hcases as [Hle1 | [Hk2 | [Hk3 | [Hk4 | [Hk5 | [Hk6 | Hge7]]]]]].
      
      * (* Case k <= 1 *)
        exact Hle1.
        
      * (* Case k = 2 *)
        subst k.
        assert (Hmod: 7 mod 2 = (x * 2) mod 2).
        { rewrite <- Hx. reflexivity. }
        rewrite Z.mod_mul in Hmod; [| lia].
        simpl in Hmod.
        discriminate.

      * (* Case k = 3 *)
        subst k.
        assert (Hmod: 7 mod 3 = (x * 3) mod 3).
        { rewrite <- Hx. reflexivity. }
        rewrite Z.mod_mul in Hmod; [| lia].
        simpl in Hmod.
        discriminate.

      * (* Case k = 4 *)
        subst k.
        assert (Hmod: 7 mod 4 = (x * 4) mod 4).
        { rewrite <- Hx. reflexivity. }
        rewrite Z.mod_mul in Hmod; [| lia].
        simpl in Hmod.
        discriminate.

      * (* Case k = 5 *)
        subst k.
        assert (Hmod: 7 mod 5 = (x * 5) mod 5).
        { rewrite <- Hx. reflexivity. }
        rewrite Z.mod_mul in Hmod; [| lia].
        simpl in Hmod.
        discriminate.

      * (* Case k = 6 *)
        subst k.
        assert (Hmod: 7 mod 6 = (x * 6) mod 6).
        { rewrite <- Hx. reflexivity. }
        rewrite Z.mod_mul in Hmod; [| lia].
        simpl in Hmod.
        discriminate.
        
      * (* Case k >= 7 *)
        lia.
Qed.