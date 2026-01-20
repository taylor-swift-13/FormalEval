Existing Coq output file content:
```coq
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Sorting.Sorted.
Require Import Coq.micromega.Lia.
Import ListNotations.

Definition is_prime (p : nat) : Prop :=
  p > 1 /\ forall d : nat, Nat.divide d p -> d = 1 \/ d = p.

Definition factorize_spec (n : nat) (factors : list nat) : Prop :=
  fold_right mult 1 factors = n /\
  Forall is_prime factors /\
  Sorted le factors.

Ltac solve_prime limit :=
  match goal with
  | [ |- is_prime ?p ] =>
    unfold is_prime; split; [ lia | ];
    intros d Hdiv;
    destruct (eq_nat_dec d 0); [ subst; destruct Hdiv; simpl in H; discriminate | ];
    let H_small := fresh "H_small" in
    assert (H_small: forall k, 2 <= k <= limit -> ~ Nat.divide k p);
    [
      intros k Hk;
      do 70 (destruct k; [
        try lia;
        intro C; apply Nat.mod_divide in C; [| lia]; vm_compute in C; discriminate
      | ]);
      lia
    |
      destruct (le_lt_dec d limit);
      [
        destruct (eq_nat_dec d 1); [left; assumption|];
        exfalso; apply (H_small d); split; lia
      |
        let k := fresh "k" in
        let Hk := fresh "Hk" in
        destruct Hdiv as [k Hk]; rewrite Nat.mul_comm in Hk;
        assert (k <= limit);
        [
          destruct (le_lt_dec k limit); [assumption|];
          assert (p >= (limit + 1) * (limit + 1));
          [ rewrite Hk; apply Nat.mul_le_mono; lia | vm_compute in H0; lia ]
        |
          destruct (eq_nat_dec k 1);
          [ subst; rewrite Nat.mul_1_l in Hk; right; symmetry; assumption |
            exfalso; apply (H_small k); split; [lia|];
            exists d; rewrite Nat.mul_comm; assumption
          ]
        ]
      ]
    ]
  end.

Example test_factorize_1003001002 : factorize_spec (2 * 181 * 631 * 4391) [2; 181; 631; 4391].
Proof.
  unfold factorize_spec.
  split.
  - (* Part 1: Product check *)
    simpl. repeat rewrite Nat.mul_assoc. rewrite Nat.mul_1_r. reflexivity.
  - split.
    + (* Part 2: Primality check *)
      constructor.
      * (* is_prime 2 *)
        solve_prime 1.
      * constructor.
        -- (* is_prime 181 *)
           solve_prime 13.
        -- constructor.
           ++ (* is_prime 631 *)
              solve_prime 25.
           ++ constructor.
              ** (* is_prime 4391 *)
                 solve_prime 66.
              ** constructor.
    + (* Part 3: Sorted check *)
      repeat constructor; lia.
Qed.