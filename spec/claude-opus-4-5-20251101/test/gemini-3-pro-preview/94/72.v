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
  skjkasdkd_spec [0; 1; 3; 4; 5; 7; 103; 8; 9] 4.
Proof.
  unfold skjkasdkd_spec.
  left.
  exists 103.
  split.
  - unfold is_largest_prime. split.
    + (* Prove 103 is in the list *)
      simpl. tauto.
    + split.
      * (* Prove 103 is prime *)
        unfold is_prime. split.
        -- lia.
        -- intros d Hle Hsq.
           (* Since d*d <= 103 and 11*11 = 121, d must be < 11 *)
           assert (d < 11).
           { destruct (Z_le_gt_dec 11 d).
             - assert (11 * 11 <= d * d) by (apply Z.mul_le_mono_nonneg; lia).
               lia.
             - lia. }
           (* Enumerate all candidates for d *)
           assert (d = 2 \/ d = 3 \/ d = 4 \/ d = 5 \/ d = 6 \/ d = 7 \/ 
                   d = 8 \/ d = 9 \/ d = 10) by lia.
           (* Verify modulo is not 0 for each candidate *)
           repeat match goal with
           | [ H : _ \/ _ |- _ ] => destruct H as [H|H]
           end; subst; vm_compute; discriminate.
      * (* Prove 103 is >= any other prime in the list *)
        intros y Hin Hp.
        simpl in Hin.
        (* Break down the list membership *)
        repeat destruct Hin as [Hin | Hin]; subst; try lia.
  - (* Prove the result calculation *)
    vm_compute. reflexivity.
Qed.