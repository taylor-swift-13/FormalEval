Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Sorting.Sorted.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

(* Helper function to extract digits from a natural number. 
   Uses fuel to ensure structural termination. *)
Fixpoint nat_to_digits_rev (n : nat) (fuel : nat) : list Z :=
  match fuel with
  | 0%nat => []
  | S f =>
    match n with
    | 0%nat => []
    | _ => Z.of_nat (n mod 10) :: nat_to_digits_rev (n / 10) f
    end
  end.

(* Helper to get the list of digits of a Z in most-significant-first order. *)
Definition get_digits (z : Z) : list Z :=
  match z with
  | 0 => [0]
  | _ => 
    let n := Z.to_nat (Z.abs z) in
    rev (nat_to_digits_rev n (S n))
  end.

(* Computes the sum of a list of integers. *)
Fixpoint sum_list (l : list Z) : Z :=
  match l with
  | [] => 0
  | h :: t => h + sum_list t
  end.

(* The weighting function defined in the Python code.
   If x >= 0, sum of digits.
   If x < 0, negate the first digit (which represents the negative sign interaction) and sum the rest. *)
Definition weight (x : Z) : Z :=
  let ds := get_digits x in
  if x <? 0 then
    match ds with
    | [] => 0 (* Unreachable for non-zero inputs *)
    | h :: t => (-h) + sum_list t
    end
  else
    sum_list ds.

(* Order relation for the stable sort.
   Compares by weight first, then by original index to ensure stability. *)
Definition weight_index_le (p1 p2 : Z * nat) : Prop :=
  let (v1, i1) := p1 in
  let (v2, i2) := p2 in
  weight v1 < weight v2 \/ (weight v1 = weight v2 /\ (i1 <= i2)%nat).

(* The main specification.
   Asserts that the result is a permutation of the input,
   sorted according to the weight and the original index (stable sort). *)
Definition order_by_points_spec (nums : list Z) (res : list Z) : Prop :=
  let indexed_nums := combine nums (seq 0 (length nums)) in
  exists indexed_res,
    Permutation indexed_nums indexed_res /\
    Sorted weight_index_le indexed_res /\
    res = map fst indexed_res.

Example test_order_by_points :
  order_by_points_spec [1; 11; -1; -11; -12] [-1; -11; 1; -12; 11].
Proof.
  unfold order_by_points_spec.
  (* The expected sorted list of pairs (value, original_index) *)
  exists [(-1, 2%nat); (-11, 3%nat); (1, 0%nat); (-12, 4%nat); (11, 1%nat)].
  
  split.
  - (* Permutation Proof *)
    (* Reduce combine and seq to get concrete lists *)
    cbn.
    
    (* Strategy: For each element in the input list (LHS), find it in the target list (RHS),
       rewrite the RHS to the form (l1 ++ x :: l2), and use Permutation_cons_app. *)

    (* 1. Input head: (1, 0) *)
    (* Target contains (1, 0) at index 2 *)
    assert (H1: [(-1, 2%nat); (-11, 3%nat); (1, 0%nat); (-12, 4%nat); (11, 1%nat)] = 
                [(-1, 2%nat); (-11, 3%nat)] ++ (1, 0%nat) :: [(-12, 4%nat); (11, 1%nat)]) by reflexivity.
    rewrite H1.
    apply Permutation_cons_app.
    simpl. (* Simplifies the list append on the RHS for the next step *)
    
    (* 2. Input head: (11, 1) *)
    (* Current RHS: [(-1, 2); (-11, 3); (-12, 4); (11, 1)] *)
    (* Target contains (11, 1) at index 3 (last) *)
    assert (H2: [(-1, 2%nat); (-11, 3%nat); (-12, 4%nat); (11, 1%nat)] = 
                [(-1, 2%nat); (-11, 3%nat); (-12, 4%nat)] ++ (11, 1%nat) :: []) by reflexivity.
    rewrite H2.
    apply Permutation_cons_app.
    simpl.

    (* 3. Input head: (-1, 2) *)
    (* Current RHS: [(-1, 2); (-11, 3); (-12, 4)] *)
    (* Target contains (-1, 2) at index 0 *)
    assert (H3: [(-1, 2%nat); (-11, 3%nat); (-12, 4%nat)] = 
                [] ++ (-1, 2%nat) :: [(-11, 3%nat); (-12, 4%nat)]) by reflexivity.
    rewrite H3.
    apply Permutation_cons_app.
    simpl.

    (* 4. Input head: (-11, 3) *)
    (* Current RHS: [(-11, 3); (-12, 4)] *)
    (* Target contains (-11, 3) at index 0 *)
    assert (H4: [(-11, 3%nat); (-12, 4%nat)] = 
                [] ++ (-11, 3%nat) :: [(-12, 4%nat)]) by reflexivity.
    rewrite H4.
    apply Permutation_cons_app.
    simpl.

    (* 5. Input head: (-12, 4) *)
    (* Current RHS: [(-12, 4)] *)
    apply Permutation_refl.

  - split.
    + (* Sorted Proof *)
      unfold weight_index_le.
      repeat constructor.
      (* Solve inequality subgoals *)
      (* Case 1: Strict weight inequality *)
      all: try (vm_compute; left; reflexivity).
      (* Case 2: Equal weight, check index *)
      all: try (vm_compute; right; split; [reflexivity | lia]).
    + (* Result Equality Proof *)
      reflexivity.
Qed.