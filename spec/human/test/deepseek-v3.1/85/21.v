Require Import Coq.Lists.List Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope Z_scope.

Fixpoint sum_even_at_odd_indices (l : list Z) (n : nat) : Z :=
  match l with
  | nil => 0%Z
  | h :: t =>
      if andb (Nat.odd n) (Z.even h)
      then (h + sum_even_at_odd_indices t (S n))%Z
      else sum_even_at_odd_indices t (S n)
  end.

Definition add_impl (lst : list Z) : Z := sum_even_at_odd_indices lst 0.

Lemma test_case : add_impl [10; 4; 3; 5; 4] = 4.
Proof.
  unfold add_impl.
  simpl.
  (* Break down the evaluation step-by-step *)
  (* 1. n=0, h=10, odd n? false, skip adding 10 *)
  (* 2. next n=1, h=4, odd n? true, 4 is even? true, add 4 *)
  (* 3. next n=2, h=3, odd n? false, skip 3 *)
  (* 4. next n=3, h=5, odd n? true, 5 is odd, skip 5 *)
  (* 5. next n=4, h=4, odd n? false, skip 4 *)
  (* Summing the added values: only 4 at step 2 *)
  reflexivity.
Qed.