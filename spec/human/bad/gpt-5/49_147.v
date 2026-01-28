Require Import ZArith.
Require Import Lia.
Open Scope Z_scope.

Definition problem_49_pre (n p : Z) : Prop := (n >= 0 /\ p > 0).

Definition problem_49_spec (n p output : Z) : Prop :=
  (n >= 0 /\ p > 0) -> output = (2 ^ n) mod p.

Example problem_49_test_1 : problem_49_spec 1000003%Z 17%Z 8%Z.
Proof.
  unfold problem_49_spec.
  intros _.
  assert (Hmod16 : (2 ^ 16) mod 17 = 1%Z) by (vm_compute; reflexivity).
  assert (Hmod3 : (2 ^ 3) mod 17 = 8%Z) by (vm_compute; reflexivity).
  assert (Hk : forall k : nat, (2 ^ (16 * Z.of_nat k)) mod 17 = 1%Z).
  {
    intro k.
    induction k as [|k IH].
    - vm_compute. reflexivity.
    - rewrite Nat2Z.inj_succ.
      replace (16 * (Z.of_nat k + 1))%Z with ((16 * Z.of_nat k) + 16)%Z by lia.
      rewrite Z.pow_add_r; [ | lia | lia ].
      rewrite Z.mul_mod by lia.
      rewrite IH, Hmod16.
      vm_compute. reflexivity.
  }
  replace 1000003%Z with (16 * 62500 + 3)%Z by (vm_compute; reflexivity).
  rewrite Z.pow_add_r; [ | lia | lia ].
  rewrite Z.mul_mod by lia.
  rewrite (Hk 62500%nat), Hmod3.
  vm_compute. reflexivity.
Qed.