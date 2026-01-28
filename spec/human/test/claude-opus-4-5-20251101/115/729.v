Require Import Coq.Lists.List Coq.Arith.Arith.
Import ListNotations.

Definition count_water (well : list nat) : nat :=
  fold_left Nat.add well 0.

Definition required_trips_impl (grid : list (list nat)) (bucket_capacity : nat) : nat :=
  fold_left
    (fun acc well =>
      let w := count_water well in
      acc + (w + bucket_capacity - 1) / bucket_capacity)
    grid
    0.

Definition problem_115_pre (grid : list (list nat)) (bucket_capacity : nat) : Prop :=
  grid <> [] /\
  bucket_capacity >= 1 /\ bucket_capacity <= 10 /\
  let len_first := length (hd [] grid) in
  len_first >= 1 /\ len_first <= 100 /\
  Forall (fun row => length row = len_first /\ Forall (fun x => x = 0 \/ x = 1) row) grid /\
  length grid >= 1 /\ length grid <= 100.
  
Definition problem_115_spec (grid : list (list nat)) (bucket_capacity : nat) (output : nat) : Prop :=
  output = required_trips_impl grid bucket_capacity.

Example test_case_2 :
  problem_115_spec [[1; 0; 1; 1]; [1; 0; 1; 1]; [1; 1; 0; 1]; [1; 0; 1; 1]; [1; 0; 1; 1]; [1; 0; 1; 1]] 3 6.
Proof.
  unfold problem_115_spec.
  unfold required_trips_impl.
  simpl.
  reflexivity.
Qed.