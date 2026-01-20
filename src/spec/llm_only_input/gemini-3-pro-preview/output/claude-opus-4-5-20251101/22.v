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

Example test_filter_integers_nested_list : filter_integers_spec [PyList] [].
Proof.
  unfold filter_integers_spec.
  split.
  - (* Check that the implementation returns the correct result *)
    simpl.
    reflexivity.
  - (* Verify the logical property *)
    intros z.
    split.
    + (* Forward direction: In z [] -> exists ... *)
      intros H_in.
      inversion H_in.
    + (* Backward direction: exists ... -> In z [] *)
      intros [v [H_in H_eq]].
      simpl in H_in.
      destruct H_in as [H_is_pylist | H_false].
      * (* Case v = PyList *)
        subst v.
        (* Now H_eq is PyList = PyInt z, which is impossible *)
        discriminate H_eq.
      * (* Case False *)
        contradiction.
Qed.