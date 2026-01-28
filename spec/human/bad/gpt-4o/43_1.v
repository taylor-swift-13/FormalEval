Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

(* Definition of pairs_sum_to_zero function *)
Fixpoint pairs_sum_to_zero (input : list Z) : bool :=
  match input with
  | [] => false
  | x :: xs =>
    if existsb (fun y => Z.eqb (x + y) 0) xs
    then true
    else pairs_sum_to_zero xs
  end.

Definition problem_43_spec (input : list Z) (output : bool) : Prop :=
  (exists i j : nat,
    (i <> j) /\
    (i < length input)%nat /\
    (j < length input)%nat /\
    (nth i input 0 + nth j input 0 = 0))
  <-> (output = true).

Example test_case_1 :
  problem_43_spec [1%Z; 3%Z; 5%Z; 0%Z] false.
Proof.
  unfold problem_43_spec.
  split.
  - intros [i [j [Hneq [Hi [Hj Heq]]]]].
    (* Analyze the possibilities for `i` and `j` *)
    assert (Hlen: length [1; 3; 5; 0] = 4) by reflexivity.
    assert (Hi_bounds: i < 4) by lia.
    assert (Hj_bounds: j < 4) by lia.
    destruct i as [| [| [| [|i]]]]; simpl in Hi_bounds; try lia;
    destruct j as [| [| [| [|j]]]]; simpl in Hj_bounds; try lia;
    simpl in Heq; lia.
  - intros Hfalse.
    exfalso.
    (* Show that all possible pairs sum to non-zero *)
    simpl in Hfalse. discriminate.
Qed.