Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Sorting.Sorted.
Require Import Lia.
Import ListNotations.
Local Open Scope Z_scope.

Definition problem_57_pre (l: list Z) : Prop := True.

Definition problem_57_spec (l: list Z) (b: bool) : Prop :=
  b = true <-> (Sorted Z.le l \/ Sorted Z.ge l).

Example problem_57_test : problem_57_spec ([1%Z; 2%Z; 4%Z; 10%Z]) true.
Proof.
  unfold problem_57_spec.
  split.
  - intros _. left.
    constructor.
    + (* HdRel Z.le 1 [2;4;10] *)
      constructor; [lia|].
      constructor; [lia|].
      constructor; [lia|].
      constructor.
    + (* Sorted Z.le [2;4;10] *)
      constructor.
      * (* HdRel Z.le 2 [4;10] *)
        constructor; [lia|].
        constructor; [lia|].
        constructor.
      * (* Sorted Z.le [4;10] *)
        constructor.
        -- (* HdRel Z.le 4 [10] *)
           constructor; [lia|].
           constructor.
        -- (* Sorted Z.le [10] *)
           constructor.
           ++ (* HdRel Z.le 10 [] *)
              constructor.
           ++ (* Sorted Z.le [] *)
              constructor.
  - intros _. reflexivity.
Qed.