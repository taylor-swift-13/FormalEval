Require Import List.
Require Import ZArith.

Import ListNotations.
Open Scope Z_scope.

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

Example test_filter_integers_mixed : 
  filter_integers_spec 
    [PyInt 4; PyDict; PyList; PyFloat; PyInt 9; PyString] 
    [4; 9].
Proof.
  unfold filter_integers_spec.
  split.
  - simpl. reflexivity.
  - intros z.
    split.
    + intros H.
      simpl in H.
      destruct H as [H4 | [H9 | H_false]].
      * subst z. exists (PyInt 4). split; [simpl; auto | reflexivity].
      * subst z. exists (PyInt 9). split; [simpl; auto 10 | reflexivity].
      * contradiction.
    + intros [v [H_in H_eq]].
      simpl in H_in.
      destruct H_in as [H1 | [H2 | [H3 | [H4 | [H5 | [H6 | H7]]]]]]; subst v; try discriminate H_eq.
      * injection H_eq as Hz. subst z. simpl. left. reflexivity.
      * injection H_eq as Hz. subst z. simpl. right. left. reflexivity.
      * contradiction.
Qed.