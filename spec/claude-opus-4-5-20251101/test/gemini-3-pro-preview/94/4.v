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
  skjkasdkd_spec [0; 724; 32; 71; 99; 32; 6; 0; 5; 91; 83; 0; 5; 6] 11.
Proof.
  unfold skjkasdkd_spec.
  left.
  exists 83.
  split.
  - unfold is_largest_prime. split.
    + simpl. tauto.
    + split.
      * unfold is_prime. split.
        -- lia.
        -- intros d Hle Hsq.
           assert (d < 10).
           { destruct (Z_le_gt_dec 10 d).
             - assert (10 * 10 <= d * d) by (apply Z.mul_le_mono_nonneg; lia).
               lia.
             - lia. }
           assert (d = 2 \/ d = 3 \/ d = 4 \/ d = 5 \/ d = 6 \/ d = 7 \/ d = 8 \/ d = 9) by lia.
           repeat match goal with
           | [ H : _ \/ _ |- _ ] => destruct H as [H|H]
           end; subst; vm_compute; discriminate.
      * intros y Hin Hp.
        simpl in Hin.
        repeat destruct Hin as [Hin | Hin]; subst; try lia.
        { (* 724 *)
          destruct Hp as [_ Hp].
          specialize (Hp 2).
          assert (2 <= 2) by lia.
          assert (2 * 2 <= 724) by lia.
          assert (724 mod 2 = 0) by (vm_compute; reflexivity).
          apply Hp in H0; [congruence | assumption].
        }
        { (* 99 *)
          destruct Hp as [_ Hp].
          specialize (Hp 3).
          assert (2 <= 3) by lia.
          assert (3 * 3 <= 99) by lia.
          assert (99 mod 3 = 0) by (vm_compute; reflexivity).
          apply Hp in H0; [congruence | assumption].
        }
        { (* 91 *)
          destruct Hp as [_ Hp].
          specialize (Hp 7).
          assert (2 <= 7) by lia.
          assert (7 * 7 <= 91) by lia.
          assert (91 mod 7 = 0) by (vm_compute; reflexivity).
          apply Hp in H0; [congruence | assumption].
        }
  - vm_compute. reflexivity.
Qed.