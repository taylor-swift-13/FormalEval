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

(* Test case: input = [[2.5%R; 4.6%R; 7.8%R; "abc"; {}; []; 7.8%R]], output = [] *)
Example test_filter_integers_mixed_types : filter_integers_spec [PyFloat; PyFloat; PyFloat; PyString; PyDict; PyList; PyFloat] [].
Proof.
  unfold filter_integers_spec.
  split.
  - simpl. reflexivity.
  - intros z. split.
    + intros H. inversion H.
    + intros [v [H_in H_eq]].
      subst v.
      simpl in H_in.
      repeat (destruct H_in as [H_contra | H_in]; [ discriminate H_contra | ]).
      contradiction.
Qed.