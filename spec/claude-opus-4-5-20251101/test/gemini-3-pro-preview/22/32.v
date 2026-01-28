Require Import List.
Require Import ZArith.

Import ListNotations.

Inductive PyValue : Type :=
  | PyInt : Z -> PyValue
  | PyFloat : PyValue
  | PyString : PyValue
  | PyDict : PyValue
  | PyList : PyValue
  | PyOther : PyValue.

Definition is_integer (v : PyValue) : bool :=
  match v with
  | PyInt _ => true
  | _ => false
  end.

Definition get_int (v : PyValue) : option Z :=
  match v with
  | PyInt n => Some n
  | _ => None
  end.

Fixpoint filter_integers_impl (values : list PyValue) : list Z :=
  match values with
  | [] => []
  | (PyInt n) :: rest => n :: filter_integers_impl rest
  | _ :: rest => filter_integers_impl rest
  end.

Definition filter_integers_spec (values : list PyValue) (result : list Z) : Prop :=
  result = filter_integers_impl values /\
  (forall z, In z result <-> exists v, In v values /\ v = PyInt z).

(* Test case: input = [4.6; 7.8; "aapplebc"; {}; []; 2.5; []], output = [] *)
Example test_filter_integers_mixed : filter_integers_spec [PyFloat; PyFloat; PyString; PyDict; PyList; PyFloat; PyList] [].
Proof.
  unfold filter_integers_spec.
  split.
  - (* Part 1: Verify the implementation returns the expected result *)
    simpl.
    reflexivity.
  - (* Part 2: Verify the logical equivalence *)
    intros z.
    split.
    + (* Direction: In z [] -> exists v ... *)
      intros H.
      inversion H.
    + (* Direction: exists v ... -> In z [] *)
      intros [v [H_in H_eq]].
      simpl in H_in.
      (* Handle all elements in the list, none are PyInt *)
      repeat (destruct H_in as [H_head | H_in]; [subst v; discriminate H_eq | ]).
      contradiction.
Qed.