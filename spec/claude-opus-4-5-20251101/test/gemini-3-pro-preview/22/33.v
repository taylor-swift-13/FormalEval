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

(* Test case: input = [[2.5; 4.17...; 7.8; "abc"; {}; []; {}]], output = [] *)
Example test_filter_integers_mixed_types : 
  filter_integers_spec [PyFloat; PyFloat; PyFloat; PyString; PyDict; PyList; PyDict] [].
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
      (* We repeat destructing the disjunctions in H_in. 
         For each element in the list, we check if it equals v.
         If so, we substitute v and check if PyFloat/String/etc = PyInt z, which is false. *)
      repeat (destruct H_in as [H_head | H_in]; [subst v; discriminate H_eq | ]).
      (* Finally, we are left with the empty list case *)
      contradiction.
Qed.