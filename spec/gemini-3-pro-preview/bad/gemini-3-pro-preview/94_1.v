Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

(* --- Specification Definitions --- *)

Definition is_prime (n : Z) : Prop :=
  1 < n /\ forall m, 1 < m < n -> n mod m <> 0.

Fixpoint digits_sum_aux (n : nat) (fuel : nat) : Z :=
  match fuel with
  | 0%nat => 0
  | S f =>
    match n with
    | 0%nat => 0
    | _ => Z.of_nat (n mod 10)%nat + digits_sum_aux (n / 10)%nat f
    end
  end.

Definition sum_digits (n : Z) : Z :=
  let val := Z.to_nat n in
  digits_sum_aux val (S val).

Definition skjkasdkd_spec (lst : list Z) (res : Z) : Prop :=
  exists p,
    In p lst /\
    is_prime p /\
    (forall q, In q lst -> is_prime q -> q <= p) /\
    res = sum_digits p.

(* --- Helper Definitions for Primality Checking --- *)

(* A computational function to check if n has no divisors in [m, n) *)
Fixpoint check_divisors_iter (n : Z) (m : Z) (fuel : nat) : bool :=
  match fuel with
  | O => false (* Should not happen if fuel is sufficient *)
  | S f =>
    if m >=? n then true
    else if n mod m =? 0 then false
    else check_divisors_iter n (m + 1) f
  end.

Lemma check_divisors_iter_correct : forall fuel n m,
  check_divisors_iter n m fuel = true ->
  forall k, m <= k < n -> n mod k <> 0.
Proof.
  induction fuel; intros n m Hres k Hrange.
  - simpl in Hres. discriminate.
  - simpl in Hres.
    destruct (m >=? n) eqn:Hge.
    + apply Z.geb_le in Hge. lia.
    + destruct (n mod m =? 0) eqn:Hdiv.
      * discriminate.
      * apply Z.eqb_neq in Hdiv.
        destruct (Z.eq_dec m k).
        -- subst. assumption.
        -- apply IHfuel with (m := m + 1); try assumption.
           lia.
Qed.

(* --- Test Case and Proof --- *)

Definition input_list : list Z := 
  [0; 3; 2; 1; 3; 5; 7; 4; 5; 5; 5; 2; 181; 32; 4; 32; 3; 2; 32; 324; 4; 3].

Example test_skjkasdkd : skjkasdkd_spec input_list 10.
Proof.
  unfold skjkasdkd_spec.
  exists 181.
  split.
  { (* 1. Prove 181 is in the list *)
    unfold input_list.
    repeat (simpl; tauto).
  }
  split.
  { (* 2. Prove 181 is prime *)
    unfold is_prime. split.
    - lia. (* 1 < 181 *)
    - (* Use the helper lemma for computability *)
      apply check_divisors_iter_correct with (fuel := 200%nat) (m := 2).
      vm_compute. reflexivity.
  }
  split.
  { (* 3. Prove 181 is the maximum prime in the list *)
    intros q Hin Hprime.
    unfold input_list in Hin.
    (* Break down the list membership into cases *)
    repeat (destruct Hin as [H | Hin]; [subst q | ]); try lia; try contradiction.
    
    (* The only case not solved by lia is 324, because 324 > 181.
       We must prove 324 is not prime. *)
    exfalso.
    unfold is_prime in Hprime.
    destruct Hprime as [_ Hdiv].
    (* 324 is divisible by 2 *)
    specialize (Hdiv 2).
    assert (1 < 2 < 324) by lia.
    apply Hdiv in H.
    vm_compute in H. congruence.
  }
  { (* 4. Prove sum_digits 181 = 10 *)
    unfold sum_digits, digits_sum_aux.
    vm_compute.
    reflexivity.
  }
Qed.