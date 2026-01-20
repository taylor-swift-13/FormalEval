Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.

Import ListNotations.
Open Scope Z_scope.

Definition signZ (x : Z) : Z :=
  match Z.compare x 0 with
  | Lt => -1
  | Eq => 0
  | Gt => 1
  end.

Fixpoint sum_abs (l : list Z) : Z :=
  match l with
  | [] => 0
  | x :: xs => Z.abs x + sum_abs xs
  end.

Fixpoint prod_sign (l : list Z) : Z :=
  match l with
  | [] => 1
  | x :: xs => signZ x * prod_sign xs
  end.

Definition prod_signs_spec (arr : list Z) (res : option Z) : Prop :=
  (arr = [] /\ res = None) \/
  (In 0 arr /\ res = Some 0) \/
  (~ In 0 arr /\ arr <> [] /\ res = Some (sum_abs arr * prod_sign arr)).

Example test_case_1: prod_signs_spec [1; 2; 2; -4] (Some (-9)).
Proof.
  (* Unfold the specification *)
  unfold prod_signs_spec.
  
  (* Select the third branch of the disjunction *)
  right. right.
  
  (* Split the conjunctions manually to avoid bullet errors *)
  split.
  - (* Subgoal 1: ~ In 0 [1; 2; 2; -4] *)
    intro H.
    simpl in H.
    (* Destruct the disjunctions from In and solve equalities with lia *)
    repeat destruct H as [H | H]; try lia.
    
  - (* Remaining conjunction: arr <> [] /\ res = ... *)
    split.
    + (* Subgoal 2: [1; 2; 2; -4] <> [] *)
      discriminate.
      
    + (* Subgoal 3: res = Some (sum_abs ... * prod_sign ...) *)
      simpl.
      (* sum_abs = 1+2+2+4 = 9 *)
      (* prod_sign = 1*1*1*(-1) = -1 *)
      (* 9 * -1 = -9 *)
      reflexivity.
Qed.