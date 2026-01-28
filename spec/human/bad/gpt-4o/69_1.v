Require Import ZArith.
Require Import List.
Import ListNotations.

Open Scope Z_scope.

Fixpoint count (z : Z) (lst : list Z) : nat :=
  match lst with
  | [] => 0
  | h :: t => (if Z.eqb z h then 1 else 0) + count z t
  end.

Fixpoint find_max_satisfying (lst : list Z) (candidates : list Z) (current_max : Z) : Z :=
  match candidates with
  | [] => current_max
  | h :: t =>
      if Z.of_nat (count h lst) >=? h then
        find_max_satisfying lst t (Z.max h current_max)
      else
        find_max_satisfying lst t current_max
  end.

Definition search_impl (lst : list Z) : Z :=
  match lst with
  | [] => (-1)%Z
  | _ =>
      let candidates := lst in
      let max_val := find_max_satisfying lst candidates (-1)%Z in
      if max_val =? (-1)%Z then
        (-1)%Z
      else
        max_val
  end.

Definition problem_69_pre (lst : list Z) : Prop := lst <> []%list /\ (forall x, In x lst -> (x > 0)%Z).

Definition problem_69_spec (lst : list Z) (y : Z) : Prop :=
  y = search_impl lst.

Example test_case_search :
  problem_69_spec [5%Z; 5%Z; 5%Z; 5%Z; 1%Z] 1%Z.
Proof.
  unfold problem_69_spec.
  unfold search_impl.
  simpl.
  unfold find_max_satisfying.
  simpl.
  (* Evaluate count for each candidate *)
  assert (count 5 [5; 5; 5; 5; 1] = 4).
  { simpl. reflexivity. }
  assert (count 1 [5; 5; 5; 5; 1] = 1).
  { simpl. reflexivity. }
  (* Check each candidate against the condition *)
  (* For candidate 5 *)
  assert (Z.of_nat (count 5 [5; 5; 5; 5; 1]) <? 5 = true).
  { simpl. lia. }
  rewrite H1. simpl.
  (* For candidate 1 *)
  assert (Z.of_nat (count 1 [5; 5; 5; 5; 1]) >=? 1 = true).
  { simpl. lia. }
  rewrite H2. simpl.
  reflexivity.
Qed.