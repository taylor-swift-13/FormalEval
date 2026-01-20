Require Import List ZArith.
Import ListNotations.

Fixpoint factorial (n : nat) : nat :=
  match n with
  | O => 1
  | S n' => n * factorial n'
  end.

Fixpoint sum_to_n (n : nat) : nat :=
  match n with
  | O => 0
  | S n' => n + sum_to_n n'
  end.

Definition f_spec (n : nat) (result : list nat) : Prop :=
  result = map (fun i => if Nat.even i then factorial i else sum_to_n i) (seq 1 n).

(* Helper function to convert nat list to Z list *)
Definition nat_list_to_Z_list (l : list nat) : list Z :=
  map Z.of_nat l.

(* The test case states that for input n=5, the output should be [1; 2; 6; 24; 15] *)
Example test_f_spec_5 : 
  f_spec 5 [1; 2; 6; 24; 15].
Proof.
  unfold f_spec.
  simpl.
  reflexivity.
Qed.

(* Alternative: prove the Z version matches *)
Example test_f_spec_5_Z : 
  nat_list_to_Z_list [1; 2; 6; 24; 15] = [1%Z; 2%Z; 6%Z; 24%Z; 15%Z].
Proof.
  unfold nat_list_to_Z_list.
  simpl.
  reflexivity.
Qed.

(* Combined proof showing the full correspondence *)
Example test_f_spec_complete :
  exists result : list nat,
    f_spec 5 result /\ nat_list_to_Z_list result = [1%Z; 2%Z; 6%Z; 24%Z; 15%Z].
Proof.
  exists [1; 2; 6; 24; 15].
  split.
  - unfold f_spec. simpl. reflexivity.
  - unfold nat_list_to_Z_list. simpl. reflexivity.
Qed.