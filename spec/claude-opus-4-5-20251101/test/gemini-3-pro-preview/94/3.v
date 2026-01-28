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
  skjkasdkd_spec [1; 3; 1; 32; 5107; 34; 83278; 109; 163; 23; 2323; 32; 30; 1; 9; 3] 13.
Proof.
  unfold skjkasdkd_spec.
  left.
  exists 5107.
  split.
  - unfold is_largest_prime. split.
    + simpl. tauto.
    + split.
      * unfold is_prime. split.
        -- lia.
        -- intros d Hle Hsq.
           assert (d < 72).
           { destruct (Z_le_gt_dec 72 d).
             - assert (72 * 72 <= d * d) by (apply Z.mul_le_mono_nonneg; lia).
               lia.
             - lia. }
           assert (d = 2 \/ d = 3 \/ d = 4 \/ d = 5 \/ d = 6 \/ d = 7 \/ d = 8 \/ d = 9 \/ d = 10 \/
                   d = 11 \/ d = 12 \/ d = 13 \/ d = 14 \/ d = 15 \/ d = 16 \/ d = 17 \/ d = 18 \/ d = 19 \/
                   d = 20 \/ d = 21 \/ d = 22 \/ d = 23 \/ d = 24 \/ d = 25 \/ d = 26 \/ d = 27 \/ d = 28 \/
                   d = 29 \/ d = 30 \/ d = 31 \/ d = 32 \/ d = 33 \/ d = 34 \/ d = 35 \/ d = 36 \/ d = 37 \/
                   d = 38 \/ d = 39 \/ d = 40 \/ d = 41 \/ d = 42 \/ d = 43 \/ d = 44 \/ d = 45 \/ d = 46 \/
                   d = 47 \/ d = 48 \/ d = 49 \/ d = 50 \/ d = 51 \/ d = 52 \/ d = 53 \/ d = 54 \/ d = 55 \/
                   d = 56 \/ d = 57 \/ d = 58 \/ d = 59 \/ d = 60 \/ d = 61 \/ d = 62 \/ d = 63 \/ d = 64 \/
                   d = 65 \/ d = 66 \/ d = 67 \/ d = 68 \/ d = 69 \/ d = 70 \/ d = 71) by lia.
           repeat match goal with
           | [ H : _ \/ _ |- _ ] => destruct H as [H|H]
           end; subst; vm_compute; discriminate.
      * intros y Hin Hp.
        simpl in Hin.
        repeat destruct Hin as [Hin | Hin]; subst; try lia.
        {
          destruct Hp as [_ Hp].
          specialize (Hp 2).
          assert (2 <= 2) by lia.
          assert (2 * 2 <= 83278) by lia.
          assert (83278 mod 2 = 0) by (vm_compute; reflexivity).
          apply Hp in H0; [congruence | assumption].
        }
  - vm_compute. reflexivity.
Qed.