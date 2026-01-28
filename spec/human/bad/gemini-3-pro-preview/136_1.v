Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

(* a 是 lst 中最大的负整数（Some z）或不存在负整数（None） *)
Definition is_largest_negative (lst : list Z) (a : option Z) : Prop :=
  match a with
  | Some z => z < 0 /\ In z lst /\ (forall x, In x lst -> x < 0 -> x <= z)
  | None   => forall x, In x lst -> ~(x < 0)
  end.

(* b 是 lst 中最小的正整数（Some z）或不存在正整数（None） *)
Definition is_smallest_positive (lst : list Z) (b : option Z) : Prop :=
  match b with
  | Some z => z > 0 /\ In z lst /\ (forall x, In x lst -> x > 0 -> z <= x)
  | None   => forall x, In x lst -> ~(x > 0)
  end.

(* 任意整数列表均可 *)
Definition problem_136_pre (lst : list Z) : Prop := True.

(* 最终 Spec：结果 res = (a, b) 当且仅当 a 是最大的负整数（或 None），b 是最小的正整数（或 None） *)
Definition problem_136_spec (lst : list Z) (res : option Z * option Z) : Prop :=
  let (a, b) := res in
  is_largest_negative lst a /\ is_smallest_positive lst b.

(* Test case verification *)
Example test_problem_136 : problem_136_spec [2; 4; 1; 3; 5; 7] (None, Some 1).
Proof.
  (* Unfold the main specification *)
  unfold problem_136_spec.
  
  (* Split the proof into two parts: negative check and positive check *)
  split.
  
  - (* Part 1: Verify is_largest_negative for None *)
    unfold is_largest_negative.
    intros x H_in.
    (* Simplify the list membership hypothesis to a disjunction of equalities *)
    simpl in H_in.
    (* Use intuition with lia to handle all cases in the disjunction automatically.
       This avoids manual destruction loops and prevents "No such goal" errors. *)
    intuition lia.

  - (* Part 2: Verify is_smallest_positive for Some 1 *)
    unfold is_smallest_positive.
    repeat split.
    + (* Subgoal 2.1: 1 > 0 *)
      lia.
    + (* Subgoal 2.2: In 1 [2; 4; 1; 3; 5; 7] *)
      simpl. auto.
    + (* Subgoal 2.3: For all x in list, if x > 0 then 1 <= x *)
      intros x H_in H_pos.
      simpl in H_in.
      (* Again, use intuition lia to check 1 <= x for all x in the list *)
      intuition lia.
Qed.