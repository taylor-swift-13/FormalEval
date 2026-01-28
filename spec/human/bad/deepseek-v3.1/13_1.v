Require Import ZArith.
Require Import Lia.
Open Scope Z_scope.

Definition problem_13_pre (a b : Z) : Prop :=
  a <> 0 \/ b <> 0.

Definition problem_13_spec (a b output : Z) : Prop :=
  (output mod a = 0) /\
  (output mod b = 0) /\
  (forall x : Z, (x mod a = 0) -> (x mod b = 0) -> x > 0 -> x <= output).

Example test_case : problem_13_spec 3 7 1.
Proof.
  unfold problem_13_spec.
  split.
  - (* output mod a = 0 *)
    compute. reflexivity.
  - split.
    + (* output mod b = 0 *)
      compute. reflexivity.
    + (* ∀ x, (x mod a = 0 ∧ x mod b = 0) → x ≤ output *)
      intros x H1 H2 H3.
      (* x must divide both a and b *)
      assert (Z.divide x 3) as Hdiv1.
      { apply Z.mod_divide. intro H. subst x. compute in H3. lia. exact H1. }
      assert (Z.divide x 7) as Hdiv2.
      { apply Z.mod_divide. intro H. subst x. compute in H3. lia. exact H2. }
      
      (* Since x divides both 3 and 7, it must divide their gcd *)
      assert (Z.divide x (Z.gcd 3 7)) as Hdiv_gcd.
      { apply Z.gcd_greatest; assumption. }
      
      (* Compute gcd(3, 7) = 1 *)
      compute in Hdiv_gcd.
      
      (* x divides 1 and x > 0, so x must be 1 *)
      assert (x = 1 \/ x = -1) as Hcases.
      { apply Z.divide_1_r; assumption. }
      
      destruct Hcases.
      * (* Case x = 1 *)
        subst x. lia.
      * (* Case x = -1 *)
        subst x. compute in H3. lia.  (* Contradicts x > 0 *)
Qed.