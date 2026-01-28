Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Lia.
Import ListNotations.
Open Scope Z_scope.

(* Helper to define factorial using structural recursion on nat for Z *)
Fixpoint factorial_nat (k : nat) : Z :=
  match k with
  | 0%nat => 1
  | S k' => (Z.of_nat k) * factorial_nat k'
  end.

Definition factorial (k : Z) : Z := factorial_nat (Z.to_nat k).

(* Helper to define sum using structural recursion on nat for Z *)
Fixpoint sum_1_to_i_nat (i : nat) : Z :=
  match i with
  | 0%nat => 0
  | S i' => (Z.of_nat i) + sum_1_to_i_nat i'
  end.

Definition sum_1_to_i (i : Z) : Z := sum_1_to_i_nat (Z.to_nat i).

Definition f_spec (n : Z) (l : list Z) : Prop :=
  Z.of_nat (length l) = n /\
  (forall i, 1 <= i <= n ->
    nth (Z.to_nat (i-1)) l 0 = 
      if Z.even i then factorial i else sum_1_to_i i).

Example test_case : f_spec 19 [1; 2; 6; 24; 15; 720; 28; 40320; 45; 3628800; 66; 479001600; 91; 87178291200; 120; 20922789888000; 153; 6402373705728000; 190].
Proof.
  unfold f_spec.
  split.
  - (* Check length *)
    simpl. reflexivity.
  - (* Check elements *)
    intros i Hi.
    (* Break down the range 1 <= i <= 19 into individual cases *)
    assert (H_cases: 
      i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ 
      i = 6 \/ i = 7 \/ i = 8 \/ i = 9 \/ i = 10 \/ 
      i = 11 \/ i = 12 \/ i = 13 \/ i = 14 \/ i = 15 \/ 
      i = 16 \/ i = 17 \/ i = 18 \/ i = 19) by lia.
    
    (* Verify each case using vm_compute for efficiency with large numbers *)
    repeat destruct H_cases as [-> | H_cases]; try (vm_compute; reflexivity).
    (* Handle the final case *)
    subst. vm_compute. reflexivity.
Qed.