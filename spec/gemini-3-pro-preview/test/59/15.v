Require Import ZArith.
Require Import Znumtheory.
Require Import Lia.
Open Scope Z_scope.

Definition largest_prime_factor_spec (n : Z) (result : Z) : Prop :=
  prime result /\ 
  (result | n) /\ 
  (forall k : Z, prime k -> (k | n) -> k <= result).

Example test_case : largest_prime_factor_spec 1024 2.
Proof.
  unfold largest_prime_factor_spec.
  split.
  - apply prime_intro.
    + lia.
    + intros n Hn.
      assert (n = 1) by lia. subst.
      apply Zgcd_1_rel_prime. compute. reflexivity.
  - split.
    + exists 512. reflexivity.
    + intros k Hk_prime Hk_div.
      repeat match goal with
      | [ H : (k | ?n) |- _ ] =>
          match n with
          | 1 => 
             apply Z.divide_1_r in H; destruct H; subst;
             destruct Hk_prime as [Hgt1 _]; lia
          | _ => 
             let half := eval compute in (n / 2) in
             replace n with (2 * half) in H by reflexivity;
             apply prime_mult in H; [| exact Hk_prime];
             destruct H as [H | H];
             [ apply Z.divide_pos_le in H; [| lia]; lia
             | ]
          end
      end.
Qed.