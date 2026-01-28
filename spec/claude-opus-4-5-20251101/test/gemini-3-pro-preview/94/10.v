Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.micromega.Lia.
Import ListNotations.

Open Scope Z_scope.

Definition is_prime (n : Z) : Prop :=
  n >= 2 /\ forall d : Z, 2 <= d -> d * d <= n -> n mod d <> 0.

Definition sum_of_digits (n : Z) : Z :=
  let fix aux (m : Z) (acc : Z) (fuel : nat) :=
    match fuel with
    | O => acc
    | S fuel' =>
      if m <=? 0 then acc
      else aux (m / 10) (acc + (m mod 10)) fuel'
    end
  in aux n 0 100%nat.

Definition is_largest_prime (x : Z) (lst : list Z) : Prop :=
  In x lst /\ is_prime x /\ forall y : Z, In y lst -> is_prime y -> y <= x.

Definition skjkasdkd_spec (lst : list Z) (result : Z) : Prop :=
  (exists x : Z, is_largest_prime x lst /\ result = sum_of_digits x) \/
  ((forall x : Z, In x lst -> ~ is_prime x) /\ result = 0).

Example test_case : 
  skjkasdkd_spec [1; 2; 3; 4; 5; 6; 7; 8; 9] 7.
Proof.
  unfold skjkasdkd_spec.
  left.
  exists 7.
  split.
  - unfold is_largest_prime. split.
    + simpl. tauto.
    + split.
      * unfold is_prime. split.
        -- lia.
        -- intros d Hle Hsq.
           assert (d < 3).
           { destruct (Z_le_gt_dec 3 d).
             - assert (3 * 3 <= d * d) by (apply Z.mul_le_mono_nonneg; lia).
               lia.
             - lia. }
           assert (d = 2) by lia.
           subst. vm_compute. discriminate.
      * intros y Hin Hp.
        simpl in Hin.
        repeat destruct Hin as [Hin | Hin]; subst; try lia.
        -- destruct Hp as [_ Hp].
           specialize (Hp 2).
           assert (2 <= 2) by lia.
           assert (2 * 2 <= 8) by lia.
           assert (8 mod 2 = 0) by (vm_compute; reflexivity).
           apply Hp in H0; [congruence | assumption].
        -- destruct Hp as [_ Hp].
           specialize (Hp 3).
           assert (2 <= 3) by lia.
           assert (3 * 3 <= 9) by lia.
           assert (9 mod 3 = 0) by (vm_compute; reflexivity).
           apply Hp in H0; [congruence | assumption].
  - vm_compute. reflexivity.
Qed.