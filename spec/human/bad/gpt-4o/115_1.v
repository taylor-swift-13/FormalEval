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

Example test_case_1 :
  problem_115_spec [[0; 0; 1; 0]; [0; 1; 0; 0]; [1; 1; 1; 1]] 1 6.
Proof.
  unfold problem_115_spec, required_trips_impl.
  simpl.
  (* Calculate total water in each well *)
  assert (count_water [0; 0; 1; 0] = 1) as H1.
  { unfold count_water. simpl. reflexivity. }
  assert (count_water [0; 1; 0; 0] = 1) as H2.
  { unfold count_water. simpl. reflexivity. }
  assert (count_water [1; 1; 1; 1] = 4) as H3.
  { unfold count_water. simpl. reflexivity. }
  (* Calculate required trips *)
  rewrite H1, H2, H3.
  (* ((1 + 1 - 1) / 1 = 1), ((1 + 1 - 1) / 1 = 1), ((4 + 1 - 1) / 1 = 4) *)
  assert ((1 + 1 - 1) / 1 = 1) as H4.
  { simpl. reflexivity. }
  assert ((4 + 1 - 1) / 1 = 4) as H5.
  { simpl. reflexivity. }
  rewrite H4, H4, H5.
  simpl.
  reflexivity.
Qed.