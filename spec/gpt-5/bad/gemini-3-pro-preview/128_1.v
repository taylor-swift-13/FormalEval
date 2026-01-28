Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.

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

Example test_prod_signs : prod_signs_spec [1; 2; 2; -4] (Some (-9)).
Proof.
  unfold prod_signs_spec.
  (* The list is not empty and does not contain 0, so we target the third branch *)
  right. right.
  repeat split.
  - (* Prove that 0 is not in the list *)
    intro H.
    simpl in H.
    (* H is a disjunction of equalities; break it down *)
    destruct H as [H | [H | [H | [H | H]]]]; try discriminate H.
    (* The last case is False, which we can destruct *)
    destruct H.
  - (* Prove that the list is not empty *)
    discriminate.
  - (* Verify the calculation *)
    simpl.
    reflexivity.
Qed.