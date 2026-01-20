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

Example test_floats_only : filter_integers_spec [PyFloat; PyFloat; PyFloat; PyFloat; PyFloat] [].
Proof.
  unfold filter_integers_spec.
  split.
  - simpl. reflexivity.
  - intros z. split.
    + simpl. intros H. contradiction.
    + intros [v [Hv Heq]]. simpl in Hv.
      destruct Hv as [H1 | [H2 | [H3 | [H4 | [H5 | H6]]]]].
      * rewrite H1 in Heq. discriminate.
      * rewrite H2 in Heq. discriminate.
      * rewrite H3 in Heq. discriminate.
      * rewrite H4 in Heq. discriminate.
      * rewrite H5 in Heq. discriminate.
      * contradiction.
Qed.