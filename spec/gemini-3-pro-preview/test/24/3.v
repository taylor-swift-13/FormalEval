Require Import Coq.ZArith.ZArith.
Require Import Psatz.

Open Scope Z_scope.

Definition largest_divisor_spec (n : Z) (result : Z) : Prop :=
  Z.divide result n /\
  result < n /\
  (forall k : Z, Z.divide k n -> k < n -> k <= result).

Example test_largest_divisor_10: largest_divisor_spec 10 5.
Proof.
  unfold largest_divisor_spec.
  split.
  - (* Prove Z.divide 5 10 *)
    exists 2. reflexivity.
  - split.
    + (* Prove 5 < 10 *)
      lia.
    + (* Prove maximality *)
      intros k Hdiv Hlt.
      destruct Hdiv as [x Hx]. (* Hx: 10 = x * k *)
      
      (* Perform case analysis on k *)
      (* We check integers between 5 and 10 *)
      assert (k <= 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k >= 10) as Hcases by lia.
      destruct Hcases as [Hle5 | [H6 | [H7 | [H8 | [H9 | Hge10]]]]].
      
      * (* Case k <= 5 *)
        exact Hle5.
        
      * (* Case k = 6 *)
        subst k.
        assert (Hmod: 10 mod 6 = (x * 6) mod 6).
        { rewrite <- Hx. reflexivity. }
        rewrite Z.mod_mul in Hmod; [| lia].
        simpl in Hmod.
        discriminate.
        
      * (* Case k = 7 *)
        subst k.
        assert (Hmod: 10 mod 7 = (x * 7) mod 7).
        { rewrite <- Hx. reflexivity. }
        rewrite Z.mod_mul in Hmod; [| lia].
        simpl in Hmod.
        discriminate.
        
      * (* Case k = 8 *)
        subst k.
        assert (Hmod: 10 mod 8 = (x * 8) mod 8).
        { rewrite <- Hx. reflexivity. }
        rewrite Z.mod_mul in Hmod; [| lia].
        simpl in Hmod.
        discriminate.
        
      * (* Case k = 9 *)
        subst k.
        assert (Hmod: 10 mod 9 = (x * 9) mod 9).
        { rewrite <- Hx. reflexivity. }
        rewrite Z.mod_mul in Hmod; [| lia].
        simpl in Hmod.
        discriminate.
        
      * (* Case k >= 10: Contradicts hypothesis k < 10 *)
        lia.
Qed.