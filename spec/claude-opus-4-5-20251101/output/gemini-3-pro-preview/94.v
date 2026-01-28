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
  skjkasdkd_spec [0; 3; 2; 1; 3; 5; 7; 4; 5; 5; 5; 2; 181; 32; 4; 32; 3; 2; 32; 324; 4; 3] 10.
Proof.
  unfold skjkasdkd_spec.
  left.
  exists 181.
  split.
  - unfold is_largest_prime. split.
    + (* Prove 181 is in the list *)
      simpl. tauto.
    + split.
      * (* Prove 181 is prime *)
        unfold is_prime. split.
        -- lia.
        -- intros d Hle Hsq.
           (* Since d*d <= 181 and 14*14 = 196, d must be < 14 *)
           assert (d < 14).
           { destruct (Z_le_gt_dec 14 d).
             - assert (14 * 14 <= d * d) by (apply Z.mul_le_mono_nonneg; lia).
               lia.
             - lia. }
           (* Enumerate all candidates for d *)
           assert (d = 2 \/ d = 3 \/ d = 4 \/ d = 5 \/ d = 6 \/ d = 7 \/ 
                   d = 8 \/ d = 9 \/ d = 10 \/ d = 11 \/ d = 12 \/ d = 13) by lia.
           (* Verify modulo is not 0 for each candidate *)
           repeat match goal with
           | [ H : _ \/ _ |- _ ] => destruct H as [H|H]
           end; subst; vm_compute; discriminate.
      * (* Prove 181 is >= any other prime in the list *)
        intros y Hin Hp.
        simpl in Hin.
        (* Break down the list membership *)
        repeat destruct Hin as [Hin | Hin]; subst; try lia.
        (* The only case where 'lia' fails is if y > 181.
           In the list, only 324 > 181. We must prove 324 is not prime. *)
        {
          destruct Hp as [_ Hp].
          specialize (Hp 2).
          assert (2 <= 2) by lia.
          assert (2 * 2 <= 324) by lia.
          assert (324 mod 2 = 0) by (vm_compute; reflexivity).
          (* 324 is divisible by 2, so it contradicts the prime property *)
          apply Hp in H0; [congruence | assumption].
        }
  - (* Prove the result calculation *)
    vm_compute. reflexivity.
Qed.