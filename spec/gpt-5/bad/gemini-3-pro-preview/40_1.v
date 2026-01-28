Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Import ListNotations.

Open Scope Z_scope.

Definition triples_sum_to_zero_spec (l : list Z) (res : bool) : Prop :=
  (res = true <-> exists (i j k : nat) (xi xj xk : Z),
    i <> j /\ i <> k /\ j <> k /\
    nth_error l i = Some xi /\
    nth_error l j = Some xj /\
    nth_error l k = Some xk /\
    xi + xj + xk = 0%Z) /\
  (res = false <-> forall (i j k : nat) (xi xj xk : Z),
    i <> j /\ i <> k /\ j <> k /\
    nth_error l i = Some xi /\
    nth_error l j = Some xj /\
    nth_error l k = Some xk ->
    xi + xj + xk <> 0%Z).

(* Tactic to iteratively destruct list indices based on nth_error *)
Ltac solve_nth :=
  match goal with
  | [ H : nth_error [] _ = Some _ |- _ ] => 
      simpl in H; discriminate
  | [ H : nth_error (_ :: _) ?n = Some _ |- _ ] =>
      destruct n; simpl in H; [ injection H as <- | ]
  end.

Example test_triples_sum_to_zero : triples_sum_to_zero_spec [1; 3; 5; 0] false.
Proof.
  unfold triples_sum_to_zero_spec.
  split.
  - (* Case: res = true <-> exists ... *)
    split; intro H.
    + (* false = true -> ... *)
      discriminate.
    + (* exists ... -> false = true *)
      destruct H as [i [j [k [xi [xj [xk [Hneq1 [Hneq2 [Hneq3 [Hnth1 [Hnth2 [Hnth3 Hsum]]]]]]]]]]]]].
      (* Decompose indices until out of bounds or resolved *)
      repeat solve_nth; 
      (* Check arithmetic contradictions *)
      lia.
  - (* Case: res = false <-> forall ... *)
    split; intro H.
    + (* false = false -> forall ... *)
      intros i j k xi xj xk [Hneq1 [Hneq2 Hneq3]] Hnth1 Hnth2 Hnth3.
      repeat solve_nth;
      lia.
    + (* forall ... -> false = false *)
      reflexivity.
Qed.